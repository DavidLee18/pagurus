//! Lower `lang-c` C11 AST into the core IR.
//!
//! Anything that cannot be modelled is an `Unsupported` node. Empty `;`
//! statements and labels are omitted; everything else is either modelled or
//! rejected. `while`/`for`/`do-while` are desugared so the condition is an
//! IR statement on the exit path (`cond; Loop[body; cond]`).

use std::collections::{HashMap, HashSet};

use lang_c::ast::{
    BinaryOperator, BlockItem, Constant, Declaration, Declarator, DeclaratorKind, DerivedDeclarator,
    Expression, ExternalDeclaration, ForInitializer, FunctionDefinition, InitDeclarator,
    Initializer, ParameterDeclaration, Statement, UnaryOperator,
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
}

impl<'a> Lowering<'a> {
    fn new(file: &'a str, source: &'a str) -> Self {
        Self {
            file,
            source,
            next_id: 1,
            spans: HashMap::new(),
            pointers: vec![HashSet::new()],
            place_scopes: vec![HashMap::new()],
            next_place: 0,
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
        if is_builtin(&name) {
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
        let body = match &def.node.statement.node {
            Statement::Compound(items) => self.lower_items(items),
            _ => self.lower_statement(&def.node.statement),
        };
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
            Statement::Return(value) => vec![Stmt::Return {
                id: self.alloc_node(stmt),
                value: value.as_ref().map(|e| self.lower_expr(e)),
            }],
            Statement::If(if_stmt) => {
                let then_branch = self.lower_statement(&if_stmt.node.then_statement);
                let else_branch = if_stmt
                    .node
                    .else_statement
                    .as_ref()
                    .map(|s| self.lower_statement(s))
                    .unwrap_or_default();
                vec![Stmt::If {
                    id: self.alloc_node(stmt),
                    cond: self.lower_expr(&if_stmt.node.condition),
                    then_branch,
                    else_branch,
                }]
            }
            Statement::While(w) => {
                // C: cond; while (true) { body; cond; } with exit after cond.
                // `SLoop` is 0+ of its body, so the header cond is required.
                let mut out = vec![self.lower_as_expr_stmt(&w.node.expression)];
                let mut loop_body = self.lower_statement(&w.node.statement);
                loop_body.push(self.lower_as_expr_stmt(&w.node.expression));
                out.push(Stmt::Loop {
                    id: self.alloc_node(stmt),
                    body: loop_body,
                });
                out
            }
            Statement::DoWhile(w) => {
                // C: body; cond; Loop[body; cond]
                let mut out = self.lower_statement(&w.node.statement);
                out.push(self.lower_as_expr_stmt(&w.node.expression));
                let mut loop_body = self.lower_statement(&w.node.statement);
                loop_body.push(self.lower_as_expr_stmt(&w.node.expression));
                out.push(Stmt::Loop {
                    id: self.alloc_node(stmt),
                    body: loop_body,
                });
                out
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
                // `for (init; cond; step) s` ≡ init; cond; Loop[s; step; cond]
                if let Some(cond) = &for_stmt.node.condition {
                    prefix.push(self.lower_as_expr_stmt(cond));
                }
                let mut loop_body = self.lower_statement(&for_stmt.node.statement);
                if let Some(step) = &for_stmt.node.step {
                    loop_body.extend(self.lower_expr_stmt(step));
                }
                if let Some(cond) = &for_stmt.node.condition {
                    loop_body.push(self.lower_as_expr_stmt(cond));
                }
                let loop_stmt = Stmt::Loop {
                    id: self.alloc_node(stmt),
                    body: loop_body,
                };
                self.pop_scope();
                let mut block_body = prefix;
                block_body.push(loop_stmt);
                vec![Stmt::Block {
                    id: self.alloc_node(stmt),
                    body: block_body,
                }]
            }
            Statement::Labeled(labeled) => self.lower_statement(&labeled.node.statement),
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
            _ => vec![self.unsupported_stmt(stmt.span, "this statement form is not modelled")],
        }
    }

    fn lower_as_expr_stmt(&mut self, expr: &Node<Expression>) -> Stmt {
        Stmt::Expr {
            id: self.alloc_node(expr),
            expr: self.lower_expr(expr),
        }
    }

    fn lower_expr_stmt(&mut self, expr: &Node<Expression>) -> Vec<Stmt> {
        match &expr.node {
            Expression::Call(call) => {
                let callee = callee_name(&call.node.callee.node);
                let args: Vec<Expr> = call
                    .node
                    .arguments
                    .iter()
                    .map(|a| self.lower_expr(a))
                    .collect();
                match callee.as_deref() {
                    Some("free") => match call.node.arguments.as_slice() {
                        [arg] if is_null_constant(arg) => {
                            // ISO C: free(NULL) is a defined no-op. We only
                            // accept a constant 0 (after peeling casts).
                            let id = self.alloc_node(expr);
                            vec![Stmt::Expr {
                                id,
                                expr: Expr::Lit { id },
                            }]
                        }
                        [arg] => match self.lower_expr(arg) {
                            Expr::Var { id, place, name } => vec![Stmt::Drop {
                                id,
                                place,
                                name,
                            }],
                            _ => vec![self.unsupported_stmt(
                                expr.span,
                                "free() of a non-variable is not modelled",
                            )],
                        },
                        _ => vec![self.unsupported_stmt(
                            expr.span,
                            "free() of a non-variable is not modelled",
                        )],
                    },
                    Some("malloc") | Some("calloc") => vec![Stmt::Expr {
                        id: self.alloc_node(expr),
                        expr: Expr::Malloc {
                            id: self.alloc_node(expr),
                            args,
                        },
                    }],
                    Some(name) => vec![Stmt::Call {
                        id: self.alloc_node(expr),
                        callee: name.to_string(),
                        args,
                    }],
                    None => vec![self.unsupported_stmt(
                        expr.span,
                        "call through a function pointer is not modelled",
                    )],
                }
            }
            Expression::BinaryOperator(bin)
                if matches!(bin.node.operator.node, BinaryOperator::Assign) =>
            {
                if let Expression::Identifier(id) = &bin.node.lhs.node {
                    vec![Stmt::Assign {
                        id: self.alloc_node(expr),
                        place: self.lookup_place(&id.node.name),
                        name: id.node.name.clone(),
                        ty: if self.is_pointer_name(&id.node.name) {
                            Ty::Pointer
                        } else {
                            Ty::Copy
                        },
                        rhs: self.lower_expr(&bin.node.rhs),
                    }]
                } else {
                    vec![self.unsupported_stmt(
                        expr.span,
                        "assignment to a non-variable place is not modelled",
                    )]
                }
            }
            _ => vec![Stmt::Expr {
                id: self.alloc_node(expr),
                expr: self.lower_expr(expr),
            }],
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
            if let Some(stmt) = self.lower_init_declarator(init_decl) {
                out.push(stmt);
            } else {
                out.push(
                    self.unsupported_stmt(init_decl.span, "declaration could not be modelled"),
                );
            }
        }
        if out.is_empty() && !decl.node.declarators.is_empty() {
            out.push(self.unsupported_stmt(decl.span, "declaration could not be modelled"));
        }
        out
    }

    fn lower_init_declarator(&mut self, init: &Node<InitDeclarator>) -> Option<Stmt> {
        let declarator = &init.node.declarator.node;
        if has_array(declarator) {
            return Some(self.unsupported_stmt(init.span, "array types are not modelled"));
        }
        let name = declarator_name(declarator)?;
        let ty = if is_pointer_declarator(declarator) {
            Ty::Pointer
        } else {
            Ty::Copy
        };
        if ty == Ty::Pointer {
            self.declare_pointer(name.clone());
        }
        let place = self.intern_place(&name);
        let init_expr = match &init.node.initializer {
            Some(Node {
                node: Initializer::Expression(expr),
                ..
            }) => Some(self.lower_expr(expr)),
            Some(_) => {
                return Some(
                    self.unsupported_stmt(init.span, "this initializer form is not modelled"),
                );
            }
            None => None,
        };
        Some(Stmt::Decl {
            id: self.alloc_node(init),
            place,
            name,
            ty,
            init: init_expr,
        })
    }

    fn lower_expr(&mut self, expr: &Node<Expression>) -> Expr {
        match &expr.node {
            Expression::Identifier(id) => {
                let name = id.node.name.clone();
                Expr::Var {
                    id: self.alloc_node(expr),
                    place: self.lookup_place(&name),
                    name,
                }
            }
            Expression::Constant(_) | Expression::StringLiteral(_) => Expr::Lit {
                id: self.alloc_node(expr),
            },
            Expression::Call(call) => {
                let callee = callee_name(&call.node.callee.node);
                let args: Vec<Expr> = call
                    .node
                    .arguments
                    .iter()
                    .map(|a| self.lower_expr(a))
                    .collect();
                match callee.as_deref() {
                    Some("malloc") | Some("calloc") => Expr::Malloc {
                        id: self.alloc_node(expr),
                        args,
                    },
                    Some("free") => self.unsupported_expr(
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
                }
            }
            Expression::UnaryOperator(unary) => {
                let inner = self.lower_expr(&unary.node.operand);
                match unary.node.operator.node {
                    UnaryOperator::Indirection => self.unsupported_expr(
                        expr.span,
                        "pointer dereference is not modelled (pagurus tracks the unique pointer, not the pointee)",
                    ),
                    UnaryOperator::Address => self.unsupported_expr(
                        expr.span,
                        "address-of is not modelled",
                    ),
                    _ => Expr::Use {
                        id: self.alloc_node(expr),
                        args: vec![inner],
                    },
                }
            }
            Expression::BinaryOperator(bin) => {
                let op = &bin.node.operator.node;
                if matches!(op, BinaryOperator::Assign) {
                    if let Expression::Identifier(id) = &bin.node.lhs.node {
                        let name = id.node.name.clone();
                        let ty = if self.is_pointer_name(&name) {
                            Ty::Pointer
                        } else {
                            Ty::Copy
                        };
                        return Expr::Assign {
                            id: self.alloc_node(expr),
                            place: self.lookup_place(&name),
                            name,
                            ty,
                            rhs: Box::new(self.lower_expr(&bin.node.rhs)),
                        };
                    }
                    return self.unsupported_expr(
                        expr.span,
                        "assignment to a non-variable place is not modelled",
                    );
                }
                if matches!(
                    op,
                    BinaryOperator::Index | BinaryOperator::Plus | BinaryOperator::Minus
                ) && (self.expr_is_pointer(&bin.node.lhs) || self.expr_is_pointer(&bin.node.rhs))
                {
                    return self.unsupported_expr(expr.span, "pointer arithmetic is not modelled");
                }
                let lhs = self.lower_expr(&bin.node.lhs);
                let rhs = self.lower_expr(&bin.node.rhs);
                Expr::Use {
                    id: self.alloc_node(expr),
                    args: vec![lhs, rhs],
                }
            }
            Expression::Cast(cast) => self.lower_expr(&cast.node.expression),
            Expression::Conditional(_) => {
                self.unsupported_expr(expr.span, "ternary (?:) is not modelled")
            }
            Expression::Comma(_) => {
                self.unsupported_expr(expr.span, "comma operator is not modelled")
            }
            Expression::Member(_) => self.unsupported_expr(
                expr.span,
                "member access of a unique pointer is not modelled",
            ),
            Expression::SizeOfTy(_) => Expr::Lit {
                id: self.alloc_node(expr),
            },
            Expression::SizeOfVal(_) => Expr::Lit {
                id: self.alloc_node(expr),
            },
            Expression::AlignOf(_) => Expr::Lit {
                id: self.alloc_node(expr),
            },
            Expression::Statement(_) => {
                self.unsupported_expr(expr.span, "GNU statement-expression is not modelled")
            }
            Expression::GenericSelection(_) => {
                self.unsupported_expr(expr.span, "_Generic is not modelled")
            }
            _ => self.unsupported_expr(expr.span, "this expression form is not modelled"),
        }
    }

    fn expr_is_pointer(&self, expr: &Node<Expression>) -> bool {
        match &expr.node {
            Expression::Identifier(id) => self.is_pointer_name(&id.node.name),
            Expression::Cast(cast) => self.expr_is_pointer(&cast.node.expression),
            _ => false,
        }
    }
}

fn is_builtin(name: &str) -> bool {
    matches!(name, "malloc" | "calloc" | "free")
}

/// True for integer constant 0, including `(void *)0` after peeling casts.
/// The identifier `NULL` is *not* recognised (it is just a name without
/// `<stddef.h>`); `free(NULL)` is therefore rejected conservatively.
fn is_null_constant(expr: &Node<Expression>) -> bool {
    match &expr.node {
        Expression::Constant(c) => match &c.node {
            Constant::Integer(int) => {
                !int.number.is_empty() && int.number.chars().all(|ch| ch == '0')
            }
            _ => false,
        },
        Expression::Cast(cast) => is_null_constant(&cast.node.expression),
        _ => false,
    }
}

fn declarator_name(decl: &Declarator) -> Option<String> {
    match &decl.kind.node {
        DeclaratorKind::Identifier(id) => Some(id.node.name.clone()),
        DeclaratorKind::Declarator(inner) => declarator_name(&inner.node),
        _ => None,
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
        _ => false,
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
        _ => false,
    }
}

fn is_function_declarator(decl: &Declarator) -> bool {
    if decl
        .derived
        .iter()
        .any(|d| matches!(d.node, DerivedDeclarator::Function(_)))
    {
        return true;
    }
    match &decl.kind.node {
        DeclaratorKind::Declarator(inner) => is_function_declarator(&inner.node),
        _ => false,
    }
}

fn function_params(decl: &Declarator) -> Vec<&Node<ParameterDeclaration>> {
    for derived in &decl.derived {
        if let DerivedDeclarator::Function(fun) = &derived.node {
            return fun.node.parameters.iter().collect();
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
    let mut lowering = Lowering::new(file, source);
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
