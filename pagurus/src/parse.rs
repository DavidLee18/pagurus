//! Allowlist lowering of the lang-c C11 AST into the core IR.
//!
//! Every `Expression` / `Statement` / `DeclaratorKind` / `DerivedDeclarator` /
//! `Initializer` / `BlockItem` / `ForInitializer` / `ExternalDeclaration`
//! variant is named. A construct is either lowered with C evaluation order
//! and conditionality, or it becomes `Unsupported`. Empty `;` is omitted.
//! Identifier labels lower the inner statement (`goto` itself is rejected).
//! `while`/`for`/`do-while` are `cond; Loop[body; cond]` so the exiting
//! condition is an IR statement. `a && b` / `a || b` become `SIf` so the
//! right-hand side is conditional. A `malloc`/`calloc`/`free` *defined* in
//! this translation unit is not treated as the synthetic allocator.

use std::collections::{HashMap, HashSet};

use lang_c::ast::{
    BinaryOperator, BlockItem, Constant, Declaration, Declarator, DeclaratorKind, DerivedDeclarator,
    Expression, ExternalDeclaration, ForInitializer, FunctionDefinition, InitDeclarator,
    Initializer, Label, ParameterDeclaration, Statement, UnaryOperator,
};
use lang_c::driver::{parse_preprocessed, Config, Flavor};
use lang_c::span::{Node, Span};

use crate::diag::{display_path, SrcSpan};
use crate::hir::{Expr, Function, Param, Stmt, Ty, Unit};

#[derive(Debug)]
pub struct ParseError {
    pub message: String,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for ParseError {}

struct Lowering<'a> {
    file: &'a str,
    source: &'a str,
    next_id: u32,
    spans: HashMap<u32, SrcSpan>,
    pointers: Vec<HashSet<String>>,
    place_scopes: Vec<HashMap<String, u32>>,
    next_place: u32,
    /// Function names with a body in this TU. Synthetic `malloc`/`calloc`/`free`
    /// lowering is suppressed for these so a user definition cannot masquerade.
    defined_funs: HashSet<String>,
}

impl<'a> Lowering<'a> {
    fn new(file: &'a str, source: &'a str, defined_funs: HashSet<String>) -> Self {
        Self {
            file,
            source,
            next_id: 1,
            spans: HashMap::new(),
            pointers: vec![HashSet::new()],
            place_scopes: vec![HashMap::new()],
            next_place: 0,
            defined_funs,
        }
    }

    fn alloc(&mut self, span: Span) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        self.spans
            .insert(id, SrcSpan::from_offset(self.file, self.source, span.start));
        id
    }

    fn alloc_node<T>(&mut self, node: &Node<T>) -> u32 {
        self.alloc(node.span)
    }

    fn is_pointer_name(&self, name: &str) -> bool {
        self.pointers.iter().rev().any(|s| s.contains(name))
    }

    fn declare_pointer(&mut self, name: String) {
        if let Some(scope) = self.pointers.last_mut() {
            scope.insert(name);
        }
    }

    fn intern_place(&mut self, name: &str) -> u32 {
        let id = self.next_place;
        self.next_place += 1;
        if let Some(scope) = self.place_scopes.last_mut() {
            scope.insert(name.to_string(), id);
        }
        id
    }

    fn lookup_place(&mut self, name: &str) -> u32 {
        for scope in self.place_scopes.iter().rev() {
            if let Some(&id) = scope.get(name) {
                return id;
            }
        }
        self.intern_place(name)
    }

    fn push_scope(&mut self) {
        self.pointers.push(HashSet::new());
        self.place_scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.pointers.pop();
        self.place_scopes.pop();
    }

    fn unsupported_expr(&mut self, span: Span, reason: impl Into<String>) -> Expr {
        Expr::Unsupported {
            id: self.alloc(span),
            reason: reason.into(),
        }
    }

    fn unsupported_stmt(&mut self, span: Span, reason: impl Into<String>) -> Stmt {
        Stmt::Unsupported {
            id: self.alloc(span),
            reason: reason.into(),
        }
    }

    fn synth_alloc(&self, name: &str) -> bool {
        matches!(name, "malloc" | "calloc") && !self.defined_funs.contains(name)
    }

    fn synth_free(&self, name: &str) -> bool {
        name == "free" && !self.defined_funs.contains(name)
    }

    fn synth_realloc(&self, name: &str) -> bool {
        name == "realloc" && !self.defined_funs.contains(name)
    }

    fn synth_builtin_proto(&self, name: &str) -> bool {
        self.synth_alloc(name) || self.synth_free(name) || self.synth_realloc(name)
    }

    fn wrap_expr(&mut self, origin: &Node<Expression>, expr: Expr) -> Stmt {
        Stmt::Expr {
            id: self.alloc_node(origin),
            expr,
        }
    }

    fn lower_unit(&mut self, tu: &lang_c::ast::TranslationUnit) -> Unit {
        let mut by_name: HashMap<String, Function> = HashMap::new();
        let mut extras: Vec<Stmt> = Vec::new();
        for ext in &tu.0 {
            match &ext.node {
                ExternalDeclaration::FunctionDefinition(def) => {
                    if let Some(fun) = self.lower_function(def, true) {
                        by_name.insert(fun.name.clone(), fun);
                    }
                }
                ExternalDeclaration::Declaration(decl) => {
                    for init in &decl.node.declarators {
                        let d = &init.node.declarator.node;
                        if is_function_declarator(d) {
                            if let Some(fun) = self.lower_function_decl(init) {
                                by_name.entry(fun.name.clone()).or_insert(fun);
                            }
                        } else {
                            extras.push(self.unsupported_stmt(
                                init.span,
                                format!(
                                    "global declaration of `{}` is not modelled",
                                    declarator_name(d).unwrap_or_else(|| "<anon>".into())
                                ),
                            ));
                        }
                    }
                }
                ExternalDeclaration::StaticAssert(_) => {
                    extras.push(self.unsupported_stmt(ext.span, "static_assert is not modelled"));
                }
            }
        }
        let mut functions: Vec<Function> = by_name.into_values().collect();
        if !extras.is_empty() {
            functions.push(Function {
                id: self.alloc(Span { start: 0, end: 0 }),
                name: "__pagurus_globals".into(),
                defined: true,
                params: Vec::new(),
                body: extras,
            });
        }
        functions.sort_by(|a, b| a.name.cmp(&b.name));
        Unit {
            file: self.file.to_string(),
            functions,
            spans: std::mem::take(&mut self.spans),
        }
    }

    fn lower_function_decl(&mut self, init: &Node<InitDeclarator>) -> Option<Function> {
        let d = &init.node.declarator.node;
        let name = declarator_name(d)?;
        if self.synth_builtin_proto(&name) {
            return None;
        }
        let params = function_params(d)
            .into_iter()
            .filter_map(|p| self.lower_param(p))
            .collect();
        Some(Function {
            id: self.alloc_node(init),
            name,
            defined: false,
            params,
            body: Vec::new(),
        })
    }

    fn lower_function(
        &mut self,
        def: &Node<FunctionDefinition>,
        defined: bool,
    ) -> Option<Function> {
        let name = declarator_name(&def.node.declarator.node)?;
        self.push_scope();
        let params = function_params(&def.node.declarator.node)
            .into_iter()
            .filter_map(|p| {
                let param = self.lower_param(p);
                if let Some(p) = &param {
                    if p.ty == Ty::Pointer {
                        self.declare_pointer(p.name.clone());
                    }
                }
                param
            })
            .collect();
        let mut body = match &def.node.statement.node {
            Statement::Compound(items) => self.lower_items(items),
            _ => self.lower_statement(&def.node.statement),
        };
        if !def.node.declarations.is_empty() {
            body.insert(
                0,
                self.unsupported_stmt(
                    def.span,
                    "K&R parameter declarations are not modelled",
                ),
            );
        }
        self.pop_scope();
        Some(Function {
            id: self.alloc_node(def),
            name,
            defined,
            params,
            body,
        })
    }

    fn lower_param(&mut self, param: &Node<ParameterDeclaration>) -> Option<Param> {
        let decl = param.node.declarator.as_ref()?;
        let name = declarator_name(&decl.node)?;
        if name == "void" {
            return None;
        }
        if has_array(&decl.node) {
            return Some(Param {
                id: self.alloc_node(decl),
                place: self.intern_place(&name),
                name,
                ty: Ty::Copy,
            });
        }
        if has_block_or_kr(&decl.node) {
            return None;
        }
        let ty = if is_pointer_declarator(&decl.node) {
            Ty::Pointer
        } else {
            Ty::Copy
        };
        Some(Param {
            id: self.alloc_node(decl),
            place: self.intern_place(&name),
            name,
            ty,
        })
    }

    fn lower_items(&mut self, items: &[Node<BlockItem>]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for item in items {
            out.extend(self.lower_block_item(item));
        }
        out
    }

    fn lower_block_item(&mut self, item: &Node<BlockItem>) -> Vec<Stmt> {
        match &item.node {
            BlockItem::Declaration(decl) => self.lower_declaration(decl),
            BlockItem::Statement(stmt) => self.lower_statement(stmt),
            BlockItem::StaticAssert(_) => {
                vec![self.unsupported_stmt(item.span, "static_assert is not modelled")]
            }
        }
    }

    fn lower_statement(&mut self, stmt: &Node<Statement>) -> Vec<Stmt> {
        match &stmt.node {
            Statement::Compound(items) => {
                self.push_scope();
                let body = self.lower_items(items);
                self.pop_scope();
                vec![Stmt::Block {
                    id: self.alloc_node(stmt),
                    body,
                }]
            }
            Statement::Expression(Some(expr)) => self.lower_expr_stmt(expr),
            Statement::Expression(None) => Vec::new(),
            Statement::Return(value) => {
                let mut out = Vec::new();
                let value = match value {
                    Some(e) => {
                        let (pre, v) = self.lower_seq(e);
                        out.extend(pre);
                        Some(v)
                    }
                    None => None,
                };
                out.push(Stmt::Return {
                    id: self.alloc_node(stmt),
                    value,
                });
                out
            }
            Statement::If(if_stmt) => {
                let (mut out, cond) = self.lower_seq(&if_stmt.node.condition);
                let then_branch = self.lower_statement(&if_stmt.node.then_statement);
                let else_branch = if_stmt
                    .node
                    .else_statement
                    .as_ref()
                    .map(|s| self.lower_statement(s))
                    .unwrap_or_default();
                out.push(Stmt::If {
                    id: self.alloc_node(stmt),
                    cond,
                    then_branch,
                    else_branch,
                });
                out
            }
            Statement::While(w) => {
                let header = self.consume_seq(&w.node.expression);
                let mut loop_body = self.lower_statement(&w.node.statement);
                loop_body.extend(header.clone());
                let mut out = header;
                out.push(Stmt::Loop {
                    id: self.alloc_node(stmt),
                    body: loop_body,
                });
                out
            }
            Statement::DoWhile(w) => {
                // Lower body and condition once, then clone: same place/span ids
                // for the mandatory first iteration and the `SLoop` postfix.
                let body = self.lower_statement(&w.node.statement);
                let cond = self.consume_seq(&w.node.expression);
                let mut prefix = body.clone();
                prefix.extend(cond.clone());
                let mut loop_body = body;
                loop_body.extend(cond);
                prefix.push(Stmt::Loop {
                    id: self.alloc_node(stmt),
                    body: loop_body,
                });
                prefix
            }
            Statement::For(for_stmt) => {
                self.push_scope();
                let mut prefix = Vec::new();
                match &for_stmt.node.initializer.node {
                    ForInitializer::Expression(expr) => {
                        prefix.extend(self.lower_expr_stmt(expr));
                    }
                    ForInitializer::Empty => {}
                    ForInitializer::Declaration(decl) => {
                        prefix.extend(self.lower_declaration(decl));
                    }
                    ForInitializer::StaticAssert(_) => {
                        prefix.push(self.unsupported_stmt(
                            for_stmt.node.initializer.span,
                            "static_assert in for-init is not modelled",
                        ));
                    }
                }
                let header_cond = for_stmt
                    .node
                    .condition
                    .as_ref()
                    .map(|c| self.consume_seq(c))
                    .unwrap_or_default();
                prefix.extend(header_cond.clone());
                let mut loop_body = self.lower_statement(&for_stmt.node.statement);
                if let Some(step) = &for_stmt.node.step {
                    loop_body.extend(self.lower_expr_stmt(step));
                }
                loop_body.extend(header_cond);
                let loop_stmt = Stmt::Loop {
                    id: self.alloc_node(stmt),
                    body: loop_body,
                };
                self.pop_scope();
                prefix.push(loop_stmt);
                vec![Stmt::Block {
                    id: self.alloc_node(stmt),
                    body: prefix,
                }]
            }
            Statement::Labeled(labeled) => match &labeled.node.label.node {
                Label::Identifier(_) => self.lower_statement(&labeled.node.statement),
                Label::Case(_) | Label::CaseRange(_) | Label::Default => {
                    vec![self.unsupported_stmt(stmt.span, "switch labels are not modelled")]
                }
            },
            Statement::Goto(_) => {
                vec![self.unsupported_stmt(stmt.span, "goto is not modelled")]
            }
            Statement::Continue => {
                vec![self.unsupported_stmt(stmt.span, "continue is not modelled")]
            }
            Statement::Break => {
                vec![self.unsupported_stmt(stmt.span, "break is not modelled")]
            }
            Statement::Switch(_) => {
                vec![self.unsupported_stmt(stmt.span, "switch is not modelled")]
            }
            Statement::Asm(_) => {
                vec![self.unsupported_stmt(stmt.span, "inline assembly is not modelled")]
            }
        }
    }

    /// Evaluate `expr` for its effects (statement context).
    fn consume_seq(&mut self, expr: &Node<Expression>) -> Vec<Stmt> {
        let (mut stmts, value) = self.lower_seq(expr);
        stmts.push(self.wrap_expr(expr, value));
        stmts
    }

    fn lower_expr_stmt(&mut self, expr: &Node<Expression>) -> Vec<Stmt> {
        match &expr.node {
            Expression::Call(call) => {
                let callee = callee_name(&call.node.callee.node);
                match callee.as_deref() {
                    Some(name) if self.synth_free(name) => match call.node.arguments.as_slice() {
                        [arg] if is_null_constant(arg) => {
                            let id = self.alloc_node(expr);
                            vec![Stmt::Expr {
                                id,
                                expr: Expr::Lit { id },
                            }]
                        }
                        [arg] => {
                            let (mut pre, value) = self.lower_seq(arg);
                            match value {
                                Expr::Var { id, place, name } => {
                                    pre.push(Stmt::Drop { id, place, name });
                                    pre
                                }
                                _ => {
                                    pre.push(self.unsupported_stmt(
                                        expr.span,
                                        "free() of a non-variable is not modelled",
                                    ));
                                    pre
                                }
                            }
                        }
                        _ => vec![self.unsupported_stmt(
                            expr.span,
                            "free() of a non-variable is not modelled",
                        )],
                    },
                    Some(name) if self.synth_alloc(name) => {
                        let (mut pre, args) = self.lower_arg_list(&call.node.arguments);
                        pre.push(Stmt::Expr {
                            id: self.alloc_node(expr),
                            expr: Expr::Malloc {
                                id: self.alloc_node(expr),
                                args,
                            },
                        });
                        pre
                    }
                    Some(name) => {
                        let (mut pre, args) = self.lower_arg_list(&call.node.arguments);
                        pre.push(Stmt::Call {
                            id: self.alloc_node(expr),
                            callee: name.to_string(),
                            args,
                        });
                        pre
                    }
                    None => {
                        vec![self.unsupported_stmt(
                            expr.span,
                            "call through a function pointer is not modelled",
                        )]
                    }
                }
            }
            Expression::BinaryOperator(bin)
                if matches!(bin.node.operator.node, BinaryOperator::Assign) =>
            {
                let (mut pre, rhs) = self.lower_seq(&bin.node.rhs);
                if let Expression::Identifier(id) = &bin.node.lhs.node {
                    pre.push(Stmt::Assign {
                        id: self.alloc_node(expr),
                        place: self.lookup_place(&id.node.name),
                        name: id.node.name.clone(),
                        ty: if self.is_pointer_name(&id.node.name) {
                            Ty::Pointer
                        } else {
                            Ty::Copy
                        },
                        rhs,
                    });
                    pre
                } else {
                    pre.push(self.unsupported_stmt(
                        expr.span,
                        "assignment to a non-variable place is not modelled",
                    ));
                    pre
                }
            }
            _ => self.consume_seq(expr),
        }
    }

    fn lower_declaration(&mut self, decl: &Node<Declaration>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for init_decl in &decl.node.declarators {
            if is_function_declarator(&init_decl.node.declarator.node) {
                out.push(self.unsupported_stmt(
                    init_decl.span,
                    "nested function declaration is not modelled",
                ));
                continue;
            }
            out.extend(self.lower_init_declarator(init_decl));
        }
        if out.is_empty() && !decl.node.declarators.is_empty() {
            out.push(self.unsupported_stmt(decl.span, "declaration could not be modelled"));
        }
        out
    }

    fn lower_init_declarator(&mut self, init: &Node<InitDeclarator>) -> Vec<Stmt> {
        let declarator = &init.node.declarator.node;
        if has_array(declarator) {
            return vec![self.unsupported_stmt(init.span, "array types are not modelled")];
        }
        if has_block_or_kr(declarator) {
            return vec![self.unsupported_stmt(
                init.span,
                "this declarator form is not modelled",
            )];
        }
        let Some(name) = declarator_name(declarator) else {
            return vec![self.unsupported_stmt(init.span, "abstract declarator is not modelled")];
        };
        let ty = if is_pointer_declarator(declarator) {
            Ty::Pointer
        } else {
            Ty::Copy
        };
        if ty == Ty::Pointer {
            self.declare_pointer(name.clone());
        }
        let place = self.intern_place(&name);
        match &init.node.initializer {
            Some(Node {
                node: Initializer::Expression(expr),
                ..
            }) => {
                let (mut pre, val) = self.lower_seq(expr);
                pre.push(Stmt::Decl {
                    id: self.alloc_node(init),
                    place,
                    name,
                    ty,
                    init: Some(val),
                });
                pre
            }
            Some(Node {
                node: Initializer::List(_),
                ..
            }) => vec![self.unsupported_stmt(init.span, "this initializer form is not modelled")],
            None => vec![Stmt::Decl {
                id: self.alloc_node(init),
                place,
                name,
                ty,
                init: None,
            }],
        }
    }

    fn lower_arg_list(&mut self, args: &[Node<Expression>]) -> (Vec<Stmt>, Vec<Expr>) {
        let mut stmts = Vec::new();
        let mut out = Vec::new();
        for a in args {
            let (s, e) = self.lower_seq(a);
            stmts.extend(s);
            out.push(e);
        }
        (stmts, out)
    }

    /// Effects plus a residual value. `&&` / `||` emit `SIf` so the RHS is
    /// conditional; the residual is a dummy `Lit` (control-flow join already
    /// explores both `if` branches).
    fn lower_seq(&mut self, expr: &Node<Expression>) -> (Vec<Stmt>, Expr) {
        match &expr.node {
            Expression::Identifier(id) if id.node.name == "NULL" => (
                Vec::new(),
                Expr::Lit {
                    id: self.alloc_node(expr),
                },
            ),
            Expression::Identifier(id) => {
                let name = id.node.name.clone();
                (
                    Vec::new(),
                    Expr::Var {
                        id: self.alloc_node(expr),
                        place: self.lookup_place(&name),
                        name,
                    },
                )
            }
            Expression::Constant(_) | Expression::StringLiteral(_) => (
                Vec::new(),
                Expr::Lit {
                    id: self.alloc_node(expr),
                },
            ),
            Expression::Call(call) => {
                let callee = callee_name(&call.node.callee.node);
                let (pre, args) = self.lower_arg_list(&call.node.arguments);
                let value = match callee.as_deref() {
                    Some(name) if self.synth_alloc(name) => Expr::Malloc {
                        id: self.alloc_node(expr),
                        args,
                    },
                    Some(name) if self.synth_free(name) => self.unsupported_expr(
                        expr.span,
                        "free() used as an expression is not modelled",
                    ),
                    Some(name) => Expr::Call {
                        id: self.alloc_node(expr),
                        callee: name.to_string(),
                        args,
                    },
                    None => self.unsupported_expr(
                        expr.span,
                        "call through a function pointer is not modelled",
                    ),
                };
                (pre, value)
            }
            Expression::UnaryOperator(unary) => self.lower_unary(expr, unary),
            Expression::BinaryOperator(bin) => self.lower_binary(expr, bin),
            Expression::Cast(cast) => self.lower_seq(&cast.node.expression),
            Expression::Conditional(_) => (
                Vec::new(),
                self.unsupported_expr(expr.span, "ternary (?:) is not modelled"),
            ),
            Expression::Comma(_) => (
                Vec::new(),
                self.unsupported_expr(expr.span, "comma operator is not modelled"),
            ),
            Expression::Member(_) => (
                Vec::new(),
                self.unsupported_expr(
                    expr.span,
                    "member access of a unique pointer is not modelled",
                ),
            ),
            Expression::SizeOfTy(_) | Expression::AlignOf(_) => (
                Vec::new(),
                Expr::Lit {
                    id: self.alloc_node(expr),
                },
            ),
            Expression::SizeOfVal(_) => (
                // C does not evaluate a non-VLA `sizeof` operand; arrays/VLAs
                // are already rejected at the declarator.
                Vec::new(),
                Expr::Lit {
                    id: self.alloc_node(expr),
                },
            ),
            Expression::GenericSelection(_) => (
                Vec::new(),
                self.unsupported_expr(expr.span, "_Generic is not modelled"),
            ),
            Expression::CompoundLiteral(_) => (
                Vec::new(),
                self.unsupported_expr(expr.span, "compound literals are not modelled"),
            ),
            Expression::OffsetOf(_) => (
                Vec::new(),
                self.unsupported_expr(expr.span, "offsetof is not modelled"),
            ),
            Expression::VaArg(_) => (
                Vec::new(),
                self.unsupported_expr(expr.span, "va_arg is not modelled"),
            ),
            Expression::Statement(_) => (
                Vec::new(),
                self.unsupported_expr(expr.span, "GNU statement-expression is not modelled"),
            ),
        }
    }

    fn lower_unary(
        &mut self,
        expr: &Node<Expression>,
        unary: &Node<lang_c::ast::UnaryOperatorExpression>,
    ) -> (Vec<Stmt>, Expr) {
        match unary.node.operator.node {
            UnaryOperator::Indirection => (
                Vec::new(),
                self.unsupported_expr(
                    expr.span,
                    "pointer dereference is not modelled (pagurus tracks the unique pointer, not the pointee)",
                ),
            ),
            UnaryOperator::Address => (
                Vec::new(),
                self.unsupported_expr(expr.span, "address-of is not modelled"),
            ),
            UnaryOperator::PostIncrement
            | UnaryOperator::PostDecrement
            | UnaryOperator::PreIncrement
            | UnaryOperator::PreDecrement
                if self.expr_is_pointer(&unary.node.operand) =>
            {
                (
                    Vec::new(),
                    self.unsupported_expr(
                        expr.span,
                        "++/-- on a pointer is not modelled",
                    ),
                )
            }
            UnaryOperator::PostIncrement
            | UnaryOperator::PostDecrement
            | UnaryOperator::PreIncrement
            | UnaryOperator::PreDecrement
            | UnaryOperator::Plus
            | UnaryOperator::Minus
            | UnaryOperator::Complement
            | UnaryOperator::Negate => {
                let (pre, inner) = self.lower_seq(&unary.node.operand);
                (
                    pre,
                    Expr::Use {
                        id: self.alloc_node(expr),
                        args: vec![inner],
                    },
                )
            }
        }
    }

    fn lower_binary(
        &mut self,
        expr: &Node<Expression>,
        bin: &Node<lang_c::ast::BinaryOperatorExpression>,
    ) -> (Vec<Stmt>, Expr) {
        let op = &bin.node.operator.node;
        match op {
            BinaryOperator::Assign => {
                let (pre, rhs) = self.lower_seq(&bin.node.rhs);
                if let Expression::Identifier(id) = &bin.node.lhs.node {
                    let name = id.node.name.clone();
                    let ty = if self.is_pointer_name(&name) {
                        Ty::Pointer
                    } else {
                        Ty::Copy
                    };
                    (
                        pre,
                        Expr::Assign {
                            id: self.alloc_node(expr),
                            place: self.lookup_place(&name),
                            name,
                            ty,
                            rhs: Box::new(rhs),
                        },
                    )
                } else {
                    (
                        pre,
                        self.unsupported_expr(
                            expr.span,
                            "assignment to a non-variable place is not modelled",
                        ),
                    )
                }
            }
            BinaryOperator::LogicalAnd => {
                let (mut stmts, lhs) = self.lower_seq(&bin.node.lhs);
                let rhs_stmts = self.consume_seq(&bin.node.rhs);
                stmts.push(Stmt::If {
                    id: self.alloc_node(expr),
                    cond: lhs,
                    then_branch: rhs_stmts,
                    else_branch: Vec::new(),
                });
                (
                    stmts,
                    Expr::Lit {
                        id: self.alloc_node(expr),
                    },
                )
            }
            BinaryOperator::LogicalOr => {
                let (mut stmts, lhs) = self.lower_seq(&bin.node.lhs);
                let rhs_stmts = self.consume_seq(&bin.node.rhs);
                stmts.push(Stmt::If {
                    id: self.alloc_node(expr),
                    cond: lhs,
                    then_branch: Vec::new(),
                    else_branch: rhs_stmts,
                });
                (
                    stmts,
                    Expr::Lit {
                        id: self.alloc_node(expr),
                    },
                )
            }
            BinaryOperator::AssignPlus
            | BinaryOperator::AssignMinus
            | BinaryOperator::AssignMultiply
            | BinaryOperator::AssignDivide
            | BinaryOperator::AssignModulo
            | BinaryOperator::AssignShiftLeft
            | BinaryOperator::AssignShiftRight
            | BinaryOperator::AssignBitwiseAnd
            | BinaryOperator::AssignBitwiseXor
            | BinaryOperator::AssignBitwiseOr
                if self.expr_is_pointer(&bin.node.lhs) =>
            {
                (
                    Vec::new(),
                    self.unsupported_expr(
                        expr.span,
                        "compound assignment on a pointer is not modelled",
                    ),
                )
            }
            BinaryOperator::Index | BinaryOperator::Plus | BinaryOperator::Minus
                if self.expr_is_pointer(&bin.node.lhs) || self.expr_is_pointer(&bin.node.rhs) =>
            {
                (
                    Vec::new(),
                    self.unsupported_expr(expr.span, "pointer arithmetic is not modelled"),
                )
            }
            BinaryOperator::Index
            | BinaryOperator::Multiply
            | BinaryOperator::Divide
            | BinaryOperator::Modulo
            | BinaryOperator::Plus
            | BinaryOperator::Minus
            | BinaryOperator::ShiftLeft
            | BinaryOperator::ShiftRight
            | BinaryOperator::Less
            | BinaryOperator::Greater
            | BinaryOperator::LessOrEqual
            | BinaryOperator::GreaterOrEqual
            | BinaryOperator::Equals
            | BinaryOperator::NotEquals
            | BinaryOperator::BitwiseAnd
            | BinaryOperator::BitwiseXor
            | BinaryOperator::BitwiseOr
            | BinaryOperator::AssignPlus
            | BinaryOperator::AssignMinus
            | BinaryOperator::AssignMultiply
            | BinaryOperator::AssignDivide
            | BinaryOperator::AssignModulo
            | BinaryOperator::AssignShiftLeft
            | BinaryOperator::AssignShiftRight
            | BinaryOperator::AssignBitwiseAnd
            | BinaryOperator::AssignBitwiseXor
            | BinaryOperator::AssignBitwiseOr => {
                let (mut stmts, lhs) = self.lower_seq(&bin.node.lhs);
                let (rs, rhs) = self.lower_seq(&bin.node.rhs);
                stmts.extend(rs);
                (
                    stmts,
                    Expr::Use {
                        id: self.alloc_node(expr),
                        args: vec![lhs, rhs],
                    },
                )
            }
        }
    }

    fn expr_is_pointer(&self, expr: &Node<Expression>) -> bool {
        match &expr.node {
            Expression::Identifier(id) => self.is_pointer_name(&id.node.name),
            Expression::Cast(cast) => self.expr_is_pointer(&cast.node.expression),
            Expression::BinaryOperator(bin)
                if matches!(bin.node.operator.node, BinaryOperator::Assign) =>
            {
                self.expr_is_pointer(&bin.node.lhs)
            }
            _ => false,
        }
    }
}

fn collect_defined_names(tu: &lang_c::ast::TranslationUnit) -> HashSet<String> {
    let mut names = HashSet::new();
    for ext in &tu.0 {
        if let ExternalDeclaration::FunctionDefinition(def) = &ext.node {
            if let Some(name) = declarator_name(&def.node.declarator.node) {
                names.insert(name);
            }
        }
    }
    names
}

/// True for integer constant 0, `(void *)0` after peeling casts, and the
/// identifier `NULL` (modelled as the ISO C null pointer constant even
/// without `<stddef.h>`).
fn is_null_constant(expr: &Node<Expression>) -> bool {
    match &expr.node {
        Expression::Constant(c) => match &c.node {
            Constant::Integer(int) => {
                !int.number.is_empty() && int.number.chars().all(|ch| ch == '0')
            }
            _ => false,
        },
        Expression::Cast(cast) => is_null_constant(&cast.node.expression),
        Expression::Identifier(id) => id.node.name == "NULL",
        _ => false,
    }
}

fn declarator_name(decl: &Declarator) -> Option<String> {
    match &decl.kind.node {
        DeclaratorKind::Identifier(id) => Some(id.node.name.clone()),
        DeclaratorKind::Declarator(inner) => declarator_name(&inner.node),
        DeclaratorKind::Abstract => None,
    }
}

fn is_pointer_declarator(decl: &Declarator) -> bool {
    if decl
        .derived
        .iter()
        .any(|d| matches!(d.node, DerivedDeclarator::Pointer(_)))
    {
        return true;
    }
    match &decl.kind.node {
        DeclaratorKind::Declarator(inner) => is_pointer_declarator(&inner.node),
        DeclaratorKind::Identifier(_) | DeclaratorKind::Abstract => false,
    }
}

fn has_array(decl: &Declarator) -> bool {
    if decl
        .derived
        .iter()
        .any(|d| matches!(d.node, DerivedDeclarator::Array(_)))
    {
        return true;
    }
    match &decl.kind.node {
        DeclaratorKind::Declarator(inner) => has_array(&inner.node),
        DeclaratorKind::Identifier(_) | DeclaratorKind::Abstract => false,
    }
}

fn has_block_or_kr(decl: &Declarator) -> bool {
    if decl.derived.iter().any(|d| {
        matches!(
            d.node,
            DerivedDeclarator::KRFunction(_) | DerivedDeclarator::Block(_)
        )
    }) {
        return true;
    }
    match &decl.kind.node {
        DeclaratorKind::Declarator(inner) => has_block_or_kr(&inner.node),
        DeclaratorKind::Identifier(_) | DeclaratorKind::Abstract => false,
    }
}

fn is_function_declarator(decl: &Declarator) -> bool {
    if decl.derived.iter().any(|d| {
        matches!(
            d.node,
            DerivedDeclarator::Function(_) | DerivedDeclarator::KRFunction(_)
        )
    }) {
        return true;
    }
    match &decl.kind.node {
        DeclaratorKind::Declarator(inner) => is_function_declarator(&inner.node),
        DeclaratorKind::Identifier(_) | DeclaratorKind::Abstract => false,
    }
}

fn function_params(decl: &Declarator) -> Vec<&Node<ParameterDeclaration>> {
    for derived in &decl.derived {
        match &derived.node {
            DerivedDeclarator::Function(fun) => {
                return fun.node.parameters.iter().collect();
            }
            DerivedDeclarator::Pointer(_)
            | DerivedDeclarator::Array(_)
            | DerivedDeclarator::KRFunction(_)
            | DerivedDeclarator::Block(_) => {}
        }
    }
    if let DeclaratorKind::Declarator(inner) = &decl.kind.node {
        return function_params(&inner.node);
    }
    Vec::new()
}

fn callee_name(expr: &Expression) -> Option<String> {
    match expr {
        Expression::Identifier(id) => Some(id.node.name.clone()),
        Expression::UnaryOperator(u) => callee_name(&u.node.operand.node),
        Expression::Cast(c) => callee_name(&c.node.expression.node),
        _ => None,
    }
}

/// Replace comments with spaces so line/column offsets stay aligned with `source`.
fn strip_comments_keep_layout(source: &str) -> String {
    let chars: Vec<char> = source.chars().collect();
    let mut out = String::with_capacity(source.len());
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '"' || c == '\'' {
            out.push(c);
            i += 1;
            while i < chars.len() {
                let ch = chars[i];
                out.push(ch);
                i += 1;
                if ch == '\\' {
                    if i < chars.len() {
                        out.push(chars[i]);
                        i += 1;
                    }
                    continue;
                }
                if ch == c {
                    break;
                }
            }
            continue;
        }
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '/' {
            out.push(' ');
            out.push(' ');
            i += 2;
            while i < chars.len() && chars[i] != '\n' {
                out.push(if chars[i] == '\t' { '\t' } else { ' ' });
                i += 1;
            }
            continue;
        }
        if c == '/' && i + 1 < chars.len() && chars[i + 1] == '*' {
            out.push(' ');
            out.push(' ');
            i += 2;
            while i < chars.len() {
                if chars[i] == '\n' {
                    out.push('\n');
                    i += 1;
                    continue;
                }
                if chars[i] == '*' && i + 1 < chars.len() && chars[i + 1] == '/' {
                    out.push(' ');
                    out.push(' ');
                    i += 2;
                    break;
                }
                out.push(if chars[i] == '\t' { '\t' } else { ' ' });
                i += 1;
            }
            continue;
        }
        out.push(c);
        i += 1;
    }
    out
}

/// Parse preprocessed C (no `#include` expansion) into IR.
pub fn parse_source(file: &str, source: &str) -> Result<Unit, ParseError> {
    let config = Config {
        cpp_command: String::new(),
        cpp_options: Vec::new(),
        flavor: Flavor::StdC11,
    };
    let for_parser = strip_comments_keep_layout(source);
    let parsed = parse_preprocessed(&config, for_parser).map_err(|err| ParseError {
        message: format!(
            "failed to parse {file}:{}:{}: unexpected token, expected {}",
            err.line,
            err.column,
            format_expected(&err.expected)
        ),
    })?;
    let defined = collect_defined_names(&parsed.unit);
    let mut lowering = Lowering::new(file, source, defined);
    Ok(lowering.lower_unit(&parsed.unit))
}

pub fn parse_file(path: &std::path::Path) -> Result<Unit, ParseError> {
    let source = std::fs::read_to_string(path).map_err(|e| ParseError {
        message: format!("cannot read {}: {e}", display_path(path)),
    })?;
    parse_source(&display_path(path), &source)
}

fn format_expected(expected: &std::collections::HashSet<&'static str>) -> String {
    let mut items: Vec<_> = expected.iter().copied().collect();
    items.sort_unstable();
    items.join(", ")
}
