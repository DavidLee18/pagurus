//! Lower `lang-c` C11 AST into the v1 HIR subset.

use lang_c::ast::{
    BinaryOperator, BlockItem, Declaration, Declarator, DeclaratorKind, DerivedDeclarator,
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
}

impl Lowering<'_> {
    fn span(&self, span: Span) -> SrcSpan {
        SrcSpan::from_offset(self.file, self.source, span.start)
    }

    fn expr_span(&self, expr: &Node<Expression>) -> SrcSpan {
        self.span(expr.span)
    }

    fn lower_unit(&self, tu: &lang_c::ast::TranslationUnit) -> Unit {
        let mut functions = Vec::new();
        for ext in &tu.0 {
            if let ExternalDeclaration::FunctionDefinition(def) = &ext.node {
                if let Some(fun) = self.lower_function(def) {
                    functions.push(fun);
                }
            }
        }
        Unit {
            file: self.file.to_string(),
            functions,
        }
    }

    fn lower_function(&self, def: &Node<FunctionDefinition>) -> Option<Function> {
        let name = declarator_name(&def.node.declarator.node)?;
        let params = function_params(&def.node.declarator.node)
            .into_iter()
            .filter_map(|p| self.lower_param(p))
            .collect();
        let body = self.lower_statement(&def.node.statement);
        Some(Function {
            name,
            params,
            body,
            span: self.span(def.span),
        })
    }

    fn lower_param(&self, param: &Node<ParameterDeclaration>) -> Option<Param> {
        let decl = param.node.declarator.as_ref()?;
        let name = declarator_name(&decl.node)?;
        if name == "void" {
            return None;
        }
        Some(Param {
            name,
            ty: if is_pointer_declarator(&decl.node) {
                Ty::Pointer
            } else {
                Ty::Copy
            },
            span: self.span(decl.span),
        })
    }

    fn lower_items(&self, items: &[Node<BlockItem>]) -> Vec<Stmt> {
        let mut out = Vec::new();
        for item in items {
            out.extend(self.lower_block_item(item));
        }
        out
    }

    fn lower_statement(&self, stmt: &Node<Statement>) -> Vec<Stmt> {
        match &stmt.node {
            Statement::Compound(items) => vec![Stmt::Block(self.lower_items(items))],
            Statement::Expression(Some(expr)) => {
                vec![Stmt::Expr(self.lower_expr(expr))]
            }
            Statement::Expression(None) => Vec::new(),
            Statement::Return(value) => vec![Stmt::Return {
                value: value.as_ref().map(|e| self.lower_expr(e)),
                span: self.span(stmt.span),
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
                    cond: self.lower_expr(&if_stmt.node.condition),
                    then_branch,
                    else_branch,
                    span: self.span(stmt.span),
                }]
            }
            Statement::While(w) => {
                let mut body = vec![Stmt::Expr(self.lower_expr(&w.node.expression))];
                body.extend(self.lower_statement(&w.node.statement));
                vec![Stmt::Block(body)]
            }
            Statement::DoWhile(w) => {
                let mut body = self.lower_statement(&w.node.statement);
                body.push(Stmt::Expr(self.lower_expr(&w.node.expression)));
                vec![Stmt::Block(body)]
            }
            Statement::For(for_stmt) => {
                // Walk the loop once (v1 does not model repeated iteration).
                let mut body = Vec::new();
                match &for_stmt.node.initializer.node {
                    ForInitializer::Expression(expr) => {
                        body.push(Stmt::Expr(self.lower_expr(expr)));
                    }
                    ForInitializer::Declaration(decl) => {
                        body.extend(self.lower_declaration(decl));
                    }
                    ForInitializer::Empty | ForInitializer::StaticAssert(_) => {}
                }
                if let Some(cond) = &for_stmt.node.condition {
                    body.push(Stmt::Expr(self.lower_expr(cond)));
                }
                body.extend(self.lower_statement(&for_stmt.node.statement));
                if let Some(step) = &for_stmt.node.step {
                    body.push(Stmt::Expr(self.lower_expr(step)));
                }
                vec![Stmt::Block(body)]
            }
            Statement::Labeled(labeled) => self.lower_statement(&labeled.node.statement),
            _ => Vec::new(),
        }
    }

    fn lower_block_item(&self, item: &Node<BlockItem>) -> Vec<Stmt> {
        match &item.node {
            BlockItem::Declaration(decl) => self.lower_declaration(decl),
            BlockItem::Statement(stmt) => self.lower_statement(stmt),
            BlockItem::StaticAssert(_) => Vec::new(),
        }
    }

    fn lower_declaration(&self, decl: &Node<Declaration>) -> Vec<Stmt> {
        let mut out = Vec::new();
        for init_decl in &decl.node.declarators {
            if let Some(stmt) = self.lower_init_declarator(init_decl) {
                out.push(stmt);
            }
        }
        out
    }

    fn lower_init_declarator(&self, init: &Node<InitDeclarator>) -> Option<Stmt> {
        let declarator = &init.node.declarator.node;
        if is_function_declarator(declarator) {
            return None;
        }
        let name = declarator_name(declarator)?;
        let ty = if is_pointer_declarator(declarator) {
            Ty::Pointer
        } else {
            Ty::Copy
        };
        let init_expr = match &init.node.initializer {
            Some(Node {
                node: Initializer::Expression(expr),
                ..
            }) => Some(self.lower_expr(expr)),
            _ => None,
        };
        Some(Stmt::Decl {
            name,
            ty,
            init: init_expr,
            span: self.span(init.span),
        })
    }

    fn lower_expr(&self, expr: &Node<Expression>) -> Expr {
        let span = self.expr_span(expr);
        match &expr.node {
            Expression::Identifier(id) => Expr::Var {
                name: id.node.name.clone(),
                span,
            },
            Expression::Constant(_) | Expression::StringLiteral(_) => Expr::Lit { span },
            Expression::Call(call) => {
                let callee = callee_name(&call.node.callee.node);
                let args: Vec<Expr> = call
                    .node
                    .arguments
                    .iter()
                    .map(|a| self.lower_expr(a))
                    .collect();
                match callee.as_deref() {
                    Some("malloc") | Some("calloc") => Expr::Malloc { args, span },
                    Some("free") => {
                        let arg = args
                            .into_iter()
                            .next()
                            .unwrap_or(Expr::Lit { span: span.clone() });
                        Expr::Free {
                            arg: Box::new(arg),
                            span,
                        }
                    }
                    Some(name) => Expr::Call {
                        callee: name.to_string(),
                        args,
                        span,
                    },
                    None => Expr::Other {
                        children: args,
                        span,
                    },
                }
            }
            Expression::UnaryOperator(unary) => {
                let inner = self.lower_expr(&unary.node.operand);
                match unary.node.operator.node {
                    UnaryOperator::Indirection => Expr::Deref {
                        inner: Box::new(inner),
                        span,
                    },
                    UnaryOperator::Address => Expr::AddrOf {
                        inner: Box::new(inner),
                        span,
                    },
                    _ => Expr::Other {
                        children: vec![inner],
                        span,
                    },
                }
            }
            Expression::BinaryOperator(bin) => {
                let lhs = self.lower_expr(&bin.node.lhs);
                let rhs = self.lower_expr(&bin.node.rhs);
                if matches!(bin.node.operator.node, BinaryOperator::Assign) {
                    Expr::Assign {
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                        span,
                    }
                } else {
                    Expr::Other {
                        children: vec![lhs, rhs],
                        span,
                    }
                }
            }
            Expression::Cast(cast) => self.lower_expr(&cast.node.expression),
            Expression::Conditional(cond) => Expr::Other {
                children: vec![
                    self.lower_expr(&cond.node.condition),
                    self.lower_expr(&cond.node.then_expression),
                    self.lower_expr(&cond.node.else_expression),
                ],
                span,
            },
            Expression::Comma(items) => Expr::Other {
                children: items.iter().map(|e| self.lower_expr(e)).collect(),
                span,
            },
            Expression::Member(member) => Expr::Other {
                children: vec![self.lower_expr(&member.node.expression)],
                span,
            },
            Expression::SizeOfVal(val) => self.lower_expr(&val.node.0),
            Expression::Statement(_) => Expr::Other {
                children: Vec::new(),
                span,
            },
            _ => Expr::Lit { span },
        }
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
///
/// `lang-c`'s `parse_preprocessed` does not run a preprocessor, so `/* */` and
/// `//` comments must be stripped first.
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

/// Parse preprocessed C (no `#include` expansion) into HIR.
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
    let lowering = Lowering { file, source };
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
