//! Intra-procedural ownership analysis for unique pointer values.

use std::collections::HashMap;

use crate::diag::{Diagnostic, DiagnosticKind, Note, SrcSpan};
use crate::hir::{Expr, Function, Stmt, Ty, Unit};

#[derive(Debug, Clone)]
enum Status {
    /// No unique owner stored (uninitialized, null, or a copy type).
    Empty,
    Owned,
    Moved {
        at: SrcSpan,
    },
    Freed {
        at: SrcSpan,
    },
}

#[derive(Clone)]
struct Binding {
    ty: Ty,
    status: Status,
}

struct Analyzer {
    env: HashMap<String, Binding>,
    diags: Vec<Diagnostic>,
}

impl Analyzer {
    fn new() -> Self {
        Self {
            env: HashMap::new(),
            diags: Vec::new(),
        }
    }

    fn analyze_function(&mut self, fun: &Function) {
        self.env.clear();
        for param in &fun.params {
            self.env.insert(
                param.name.clone(),
                Binding {
                    ty: param.ty,
                    status: if param.ty == Ty::Pointer {
                        Status::Owned
                    } else {
                        Status::Empty
                    },
                },
            );
        }
        self.analyze_stmts(&fun.body);
    }

    fn analyze_stmts(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            self.analyze_stmt(stmt);
        }
    }

    fn analyze_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Decl {
                name,
                ty,
                init,
                span: _,
            } => {
                let mut status = Status::Empty;
                if let Some(init) = init {
                    if *ty == Ty::Pointer {
                        if self.take_ownership(init) {
                            status = Status::Owned;
                        }
                    } else {
                        self.use_expr(init);
                    }
                }
                self.env.insert(name.clone(), Binding { ty: *ty, status });
            }
            Stmt::Expr(expr) => {
                self.use_expr(expr);
            }
            Stmt::Return { value, .. } => {
                if let Some(expr) = value {
                    // Returning a pointer moves it out of the callee.
                    if matches!(expr, Expr::Var { name, .. } if self.is_pointer(name)) {
                        self.take_ownership(expr);
                    } else {
                        self.use_expr(expr);
                    }
                }
            }
            Stmt::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.use_expr(cond);
                let saved = self.snapshot();
                self.analyze_stmts(then_branch);
                let then_env = self.snapshot();
                self.restore(saved.clone());
                self.analyze_stmts(else_branch);
                let else_env = self.snapshot();
                self.env = merge_envs(then_env, else_env);
            }
            Stmt::Block(stmts) => self.analyze_stmts(stmts),
        }
    }

    fn snapshot(&self) -> HashMap<String, Binding> {
        self.env.clone()
    }

    fn restore(&mut self, env: HashMap<String, Binding>) {
        self.env = env;
    }

    fn is_pointer(&self, name: &str) -> bool {
        self.env
            .get(name)
            .map(|b| b.ty == Ty::Pointer)
            .unwrap_or(false)
    }

    fn use_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Var { name, span } => {
                self.check_use(name, span, UseKind::Read);
            }
            Expr::Lit { .. } => {}
            Expr::Malloc { args, .. } => {
                for arg in args {
                    self.use_expr(arg);
                }
            }
            Expr::Free { arg, span } => self.check_free(arg, span),
            Expr::Call { args, .. } => {
                for arg in args {
                    self.use_expr(arg);
                }
            }
            Expr::Assign { lhs, rhs, .. } => self.check_assign(lhs, rhs),
            Expr::Deref { inner, .. } => self.use_expr(inner),
            Expr::AddrOf { .. } => {
                // `&p` addresses the stack slot of `p`; it does not use the owned heap value.
            }
            Expr::Other { children, .. } => {
                for child in children {
                    self.use_expr(child);
                }
            }
        }
    }

    fn check_assign(&mut self, lhs: &Expr, rhs: &Expr) {
        if let Expr::Var { name, .. } = lhs {
            if self.is_pointer(name) {
                let owned = self.take_ownership(rhs);
                if let Some(binding) = self.env.get_mut(name) {
                    binding.status = if owned { Status::Owned } else { Status::Empty };
                }
                return;
            }
        }
        self.use_expr(lhs);
        self.use_expr(rhs);
    }

    /// Consume a unique pointer rvalue. Returns whether the rvalue is an owner.
    fn take_ownership(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::Malloc { args, .. } => {
                for arg in args {
                    self.use_expr(arg);
                }
                true
            }
            Expr::Var { name, span } if self.is_pointer(name) => {
                self.check_use(name, span, UseKind::Move);
                true
            }
            Expr::Assign { lhs, rhs, .. } => {
                self.check_assign(lhs, rhs);
                matches!(lhs.as_ref(), Expr::Var { name, .. } if self.is_pointer(name))
            }
            Expr::Free { arg, span } => {
                self.check_free(arg, span);
                false
            }
            other => {
                self.use_expr(other);
                false
            }
        }
    }

    fn check_free(&mut self, arg: &Expr, _span: &SrcSpan) {
        match arg {
            Expr::Var { name, span: vspan } if self.is_pointer(name) => {
                self.check_use(name, vspan, UseKind::Free { at: vspan.clone() });
            }
            Expr::Malloc { args, .. } => {
                for a in args {
                    self.use_expr(a);
                }
            }
            other => self.use_expr(other),
        }
    }

    fn check_use(&mut self, name: &str, span: &SrcSpan, kind: UseKind) {
        let Some(binding) = self.env.get(name) else {
            return;
        };
        if binding.ty != Ty::Pointer {
            return;
        }
        match (&binding.status, kind) {
            (Status::Owned, UseKind::Read) => {}
            (Status::Owned, UseKind::Move) => {
                if let Some(binding) = self.env.get_mut(name) {
                    binding.status = Status::Moved { at: span.clone() };
                }
            }
            (Status::Owned, UseKind::Free { at }) => {
                if let Some(binding) = self.env.get_mut(name) {
                    binding.status = Status::Freed { at };
                }
            }
            (Status::Moved { at }, UseKind::Free { .. }) | (Status::Moved { at }, _) => {
                let at = at.clone();
                self.report(
                    DiagnosticKind::UseAfterMove,
                    format!("use of moved value `{name}`"),
                    span.clone(),
                    vec![Note {
                        message: format!("`{name}` moved here"),
                        span: at,
                    }],
                );
            }
            (Status::Freed { at }, UseKind::Free { .. }) => {
                let at = at.clone();
                self.report(
                    DiagnosticKind::DoubleFree,
                    format!("double free of `{name}`"),
                    span.clone(),
                    vec![Note {
                        message: format!("`{name}` was freed here"),
                        span: at,
                    }],
                );
            }
            (Status::Freed { at }, _) => {
                let at = at.clone();
                self.report(
                    DiagnosticKind::UseAfterFree,
                    format!("use of freed value `{name}`"),
                    span.clone(),
                    vec![Note {
                        message: format!("`{name}` was freed here"),
                        span: at,
                    }],
                );
            }
            (Status::Empty, _) => {}
        }
    }

    fn report(&mut self, kind: DiagnosticKind, message: String, span: SrcSpan, notes: Vec<Note>) {
        self.diags.push(Diagnostic {
            kind,
            message,
            span,
            notes,
        });
    }
}

#[derive(Clone)]
enum UseKind {
    Read,
    Move,
    Free { at: SrcSpan },
}

fn merge_envs(
    mut left: HashMap<String, Binding>,
    right: HashMap<String, Binding>,
) -> HashMap<String, Binding> {
    for (name, rhs) in right {
        left.entry(name)
            .and_modify(|lhs| lhs.status = merge_status(&lhs.status, &rhs.status))
            .or_insert(rhs);
    }
    left
}

fn merge_status(a: &Status, b: &Status) -> Status {
    match (a, b) {
        (Status::Freed { at }, _) | (_, Status::Freed { at }) => Status::Freed { at: at.clone() },
        (Status::Moved { at }, _) | (_, Status::Moved { at }) => Status::Moved { at: at.clone() },
        (Status::Owned, Status::Owned) => Status::Owned,
        _ => Status::Empty,
    }
}

pub fn analyze_unit(unit: &Unit) -> Vec<Diagnostic> {
    let mut analyzer = Analyzer::new();
    for fun in &unit.functions {
        analyzer.analyze_function(fun);
    }
    analyzer.diags
}
