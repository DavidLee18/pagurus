//! Tiny C subset after lowering `lang-c`'s C11 AST.

use crate::diag::SrcSpan;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ty {
    /// Integers and other trivially copyable values.
    Copy,
    /// Pointer types modelled as unique owners (like Rust `Box`).
    Pointer,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub ty: Ty,
    pub span: SrcSpan,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
    pub span: SrcSpan,
}

#[derive(Debug, Clone)]
pub struct Unit {
    pub file: String,
    pub functions: Vec<Function>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    /// Local declaration, optionally initialized.
    Decl {
        name: String,
        ty: Ty,
        init: Option<Expr>,
        span: SrcSpan,
    },
    Expr(Expr),
    Return {
        value: Option<Expr>,
        span: SrcSpan,
    },
    If {
        cond: Expr,
        then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>,
        span: SrcSpan,
    },
    Block(Vec<Stmt>),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Var {
        name: String,
        span: SrcSpan,
    },
    Lit {
        span: SrcSpan,
    },
    /// `malloc(...)` — produces a fresh unique owner.
    Malloc {
        args: Vec<Expr>,
        span: SrcSpan,
    },
    /// `free(arg)` — consumes unique ownership of `arg`.
    Free {
        arg: Box<Expr>,
        span: SrcSpan,
    },
    /// Other calls: pointer arguments are borrowed, not moved.
    Call {
        callee: String,
        args: Vec<Expr>,
        span: SrcSpan,
    },
    Assign {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: SrcSpan,
    },
    Deref {
        inner: Box<Expr>,
        span: SrcSpan,
    },
    AddrOf {
        inner: Box<Expr>,
        span: SrcSpan,
    },
    /// Catch-all for operators we do not special-case; nested exprs are uses.
    Other {
        children: Vec<Expr>,
        span: SrcSpan,
    },
}

impl Expr {
    pub fn span(&self) -> &SrcSpan {
        match self {
            Expr::Var { span, .. }
            | Expr::Lit { span }
            | Expr::Malloc { span, .. }
            | Expr::Free { span, .. }
            | Expr::Call { span, .. }
            | Expr::Assign { span, .. }
            | Expr::Deref { span, .. }
            | Expr::AddrOf { span, .. }
            | Expr::Other { span, .. } => span,
        }
    }
}
