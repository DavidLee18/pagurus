//! Serialise the IR as the s-expression language the Idris core parses.
//!
//! Place identities are interned `Nat`s assigned by the frontend (one id
//! per binding). The original spelling is kept beside the id for messages.

use crate::hir::{Expr, Function, Param, Stmt, Ty, Unit};

pub fn emit_unit(unit: &Unit) -> String {
    let mut out = String::from("(program");
    for fun in &unit.functions {
        out.push('\n');
        emit_fun(&mut out, fun);
    }
    out.push(')');
    out.push('\n');
    out
}

fn emit_fun(out: &mut String, fun: &Function) {
    let defn = if fun.defined { "def" } else { "proto" };
    out.push_str(&format!("  (fn {} {} {defn} (params", fun.id, fun.name));
    for p in &fun.params {
        emit_param(out, p);
    }
    out.push_str(") ");
    emit_stmts(out, &fun.body);
    out.push(')');
}

fn emit_param(out: &mut String, p: &Param) {
    out.push_str(&format!(
        " (param {} {} {} {})",
        p.id,
        p.place,
        p.name,
        ty_atom(p.ty)
    ));
}

fn ty_atom(ty: Ty) -> &'static str {
    match ty {
        Ty::Pointer => "ptr",
        Ty::Copy => "copy",
    }
}

fn emit_stmts(out: &mut String, stmts: &[Stmt]) {
    out.push_str("(stmts");
    for s in stmts {
        out.push(' ');
        emit_stmt(out, s);
    }
    out.push(')');
}

fn emit_stmt(out: &mut String, stmt: &Stmt) {
    match stmt {
        Stmt::Block { id, body } => {
            out.push_str(&format!("(block {id}"));
            for s in body {
                out.push(' ');
                emit_stmt(out, s);
            }
            out.push(')');
        }
        Stmt::Decl {
            id,
            place,
            name,
            ty,
            init,
        } => {
            out.push_str(&format!("(decl {id} {place} {name} {}", ty_atom(*ty)));
            if let Some(e) = init {
                out.push(' ');
                emit_expr(out, e);
            }
            out.push(')');
        }
        Stmt::Assign {
            id,
            place,
            name,
            ty,
            rhs,
        } => {
            out.push_str(&format!(
                "(assign {id} {place} {name} {} ",
                ty_atom(*ty)
            ));
            emit_expr(out, rhs);
            out.push(')');
        }
        Stmt::Drop { id, place, name } => {
            out.push_str(&format!("(drop {id} {place} {name})"));
        }
        Stmt::Call { id, callee, args } => {
            out.push_str(&format!("(call {id} {callee}"));
            for a in args {
                out.push(' ');
                emit_expr(out, a);
            }
            out.push(')');
        }
        Stmt::Return { id, value } => {
            out.push_str(&format!("(return {id}"));
            if let Some(e) = value {
                out.push(' ');
                emit_expr(out, e);
            }
            out.push(')');
        }
        Stmt::If {
            id,
            cond,
            then_branch,
            else_branch,
        } => {
            out.push_str(&format!("(if {id} "));
            emit_expr(out, cond);
            out.push(' ');
            emit_stmts(out, then_branch);
            out.push(' ');
            emit_stmts(out, else_branch);
            out.push(')');
        }
        Stmt::Loop { id, body } => {
            out.push_str(&format!("(loop {id} "));
            emit_stmts(out, body);
            out.push(')');
        }
        Stmt::Expr { id, expr } => {
            out.push_str(&format!("(expr {id} "));
            emit_expr(out, expr);
            out.push(')');
        }
        Stmt::Unsupported { id, reason } => {
            out.push_str(&format!("(unsupported {id} {})", quote(reason)));
        }
    }
}

fn emit_expr(out: &mut String, expr: &Expr) {
    match expr {
        Expr::Var { id, place, name } => {
            out.push_str(&format!("(var {id} {place} {name})"));
        }
        Expr::Lit { id } => out.push_str(&format!("(lit {id})")),
        Expr::Null { id } => out.push_str(&format!("(null {id})")),
        Expr::Malloc { id, args } => {
            out.push_str(&format!("(malloc {id}"));
            for a in args {
                out.push(' ');
                emit_expr(out, a);
            }
            out.push(')');
        }
        Expr::Call { id, callee, args } => {
            out.push_str(&format!("(call-e {id} {callee}"));
            for a in args {
                out.push(' ');
                emit_expr(out, a);
            }
            out.push(')');
        }
        Expr::Assign {
            id,
            place,
            name,
            ty,
            rhs,
        } => {
            out.push_str(&format!(
                "(assign-e {id} {place} {name} {} ",
                ty_atom(*ty)
            ));
            emit_expr(out, rhs);
            out.push(')');
        }
        Expr::Use { id, args } => {
            out.push_str(&format!("(use {id}"));
            for a in args {
                out.push(' ');
                emit_expr(out, a);
            }
            out.push(')');
        }
        Expr::Unsupported { id, reason } => {
            out.push_str(&format!("(unsupported-e {id} {})", quote(reason)));
        }
    }
}

fn quote(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
