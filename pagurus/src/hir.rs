//! Core IR that is serialised to the Idris checker. Node ids map back to C spans.

use std::collections::HashMap;

use crate::diag::SrcSpan;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ty {
    Copy,
    Pointer,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub id: u32,
    pub place: u32,
    pub name: String,
    pub ty: Ty,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub id: u32,
    pub name: String,
    pub defined: bool,
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub struct Unit {
    pub file: String,
    pub functions: Vec<Function>,
    pub spans: HashMap<u32, SrcSpan>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Block {
        id: u32,
        body: Vec<Stmt>,
    },
    Decl {
        id: u32,
        place: u32,
        name: String,
        ty: Ty,
        init: Option<Expr>,
    },
    Assign {
        id: u32,
        place: u32,
        name: String,
        rhs: Expr,
    },
    Drop {
        id: u32,
        place: u32,
        name: String,
    },
    Call {
        id: u32,
        callee: String,
        args: Vec<Expr>,
    },
    Return {
        id: u32,
        value: Option<Expr>,
    },
    If {
        id: u32,
        cond: Expr,
        then_branch: Vec<Stmt>,
        else_branch: Vec<Stmt>,
    },
    Loop {
        id: u32,
        body: Vec<Stmt>,
    },
    Expr {
        id: u32,
        expr: Expr,
    },
    Unsupported {
        id: u32,
        reason: String,
    },
}

impl Stmt {
    pub fn id(&self) -> u32 {
        match self {
            Stmt::Block { id, .. }
            | Stmt::Decl { id, .. }
            | Stmt::Assign { id, .. }
            | Stmt::Drop { id, .. }
            | Stmt::Call { id, .. }
            | Stmt::Return { id, .. }
            | Stmt::If { id, .. }
            | Stmt::Loop { id, .. }
            | Stmt::Expr { id, .. }
            | Stmt::Unsupported { id, .. } => *id,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr {
    Var {
        id: u32,
        place: u32,
        name: String,
    },
    Lit {
        id: u32,
    },
    Malloc {
        id: u32,
        args: Vec<Expr>,
    },
    Call {
        id: u32,
        callee: String,
        args: Vec<Expr>,
    },
    Assign {
        id: u32,
        place: u32,
        name: String,
        rhs: Box<Expr>,
    },
    Use {
        id: u32,
        args: Vec<Expr>,
    },
    Unsupported {
        id: u32,
        reason: String,
    },
}

impl Expr {
    pub fn id(&self) -> u32 {
        match self {
            Expr::Var { id, .. }
            | Expr::Lit { id }
            | Expr::Malloc { id, .. }
            | Expr::Call { id, .. }
            | Expr::Assign { id, .. }
            | Expr::Use { id, .. }
            | Expr::Unsupported { id, .. } => *id,
        }
    }
}
