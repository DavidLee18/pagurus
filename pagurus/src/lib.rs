//! pagurus: a total Idris 2 ownership checker with lemmas, plus a Rust shell.
//!
//! The Idris 2 core is the only source of acceptance. This crate parses C,
//! serialises IR, and renders the core's structured diagnostics.

mod core;
mod diag;
mod emit;
mod hir;
mod parse;

pub use diag::{Diagnostic, DiagnosticKind, Label, SrcSpan};
pub use hir::Unit;
pub use parse::ParseError;

use std::path::Path;

use crate::core::check_unit;
use crate::parse::{parse_file as parse_path, parse_source};

/// Parse C and ask the Idris core whether it is safe.
pub fn check_source(filename: &str, source: &str) -> Result<Vec<Diagnostic>, ParseError> {
    let unit = parse_source(filename, source)?;
    check_unit(&unit)
}

/// Parse a C file and ask the Idris core whether it is safe.
pub fn check_file<P: AsRef<Path>>(path: P) -> Result<Vec<Diagnostic>, ParseError> {
    let unit = parse_path(path.as_ref())?;
    check_unit(&unit)
}

/// Lower C to IR without running the core (for debugging).
pub fn lower_source(filename: &str, source: &str) -> Result<Unit, ParseError> {
    parse_source(filename, source)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_use_after_move_inline() {
        let src = r#"
            void *malloc(unsigned long n);
            void free(void *p);
            int main(void) {
                void *p = malloc(4);
                void *q = p;
                free(p);
                free(q);
                return 0;
            }
        "#;
        let diags = check_source("inline.c", src).expect("parse");
        assert!(
            diags.iter().any(|d| d.kind == DiagnosticKind::UseAfterMove),
            "expected use-after-move, got {diags:?}"
        );
        let rendered = diags[0].to_string();
        assert!(rendered.contains("inline.c"));
        assert!(rendered.contains("use of moved value"));
        assert!(rendered.contains("value moved here"));
        assert!(rendered.contains("help:"));
    }

    #[test]
    fn chained_assign_moves_once() {
        let src = r#"
            void *malloc(unsigned long n);
            void free(void *p);
            int main(void) {
                void *p;
                void *q;
                q = p = malloc(8);
                free(p);
                free(q);
                return 0;
            }
        "#;
        let diags = check_source("chain.c", src).expect("parse");
        assert!(
            diags.iter().any(|d| d.kind == DiagnosticKind::UseAfterMove),
            "expected use-after-move, got {diags:?}"
        );
    }

    #[test]
    fn while_lowers_condition_before_loop() {
        let src = r#"
            void *malloc(unsigned long n);
            void free(void *p);
            int consume(int *p) { free(p); return 0; }
            int main(void) {
                int *p = malloc(4);
                while (consume(p)) {
                    p = malloc(4);
                }
                free(p);
                return 0;
            }
        "#;
        let unit = lower_source("while.c", src).expect("parse");
        let main = unit
            .functions
            .iter()
            .find(|f| f.name == "main")
            .expect("main");
        let loop_at = main
            .body
            .iter()
            .position(|s| matches!(s, crate::hir::Stmt::Loop { .. }))
            .expect("loop");
        assert!(
            loop_at > 0,
            "while must evaluate the condition before Loop, got {:?}",
            main.body
        );
        assert!(
            matches!(main.body[loop_at - 1], crate::hir::Stmt::Expr { .. }),
            "expected cond as an expr stmt immediately before Loop, got {:?}",
            main.body
        );
        match &main.body[loop_at] {
            crate::hir::Stmt::Loop { body, .. } => {
                assert!(
                    matches!(body.last(), Some(crate::hir::Stmt::Expr { .. })),
                    "Loop body must end with the condition so exit evaluates it, got {body:?}"
                );
            }
            other => panic!("expected Loop, got {other:?}"),
        }
    }

    #[test]
    fn handwritten_call_free_is_not_a_use() {
        use crate::hir::{Expr, Function, Stmt, Ty, Unit};
        use std::collections::HashMap;

        let unit = Unit {
            file: "hand.ir".into(),
            functions: vec![Function {
                id: 1,
                name: "main".into(),
                defined: true,
                params: Vec::new(),
                body: vec![
                    Stmt::Decl {
                        id: 2,
                        place: 0,
                        name: "p".into(),
                        ty: Ty::Pointer,
                        init: Some(Expr::Malloc {
                            id: 3,
                            args: vec![Expr::Lit { id: 4 }],
                        }),
                    },
                    Stmt::Call {
                        id: 5,
                        callee: "free".into(),
                        args: vec![Expr::Var {
                            id: 6,
                            place: 0,
                            name: "p".into(),
                        }],
                    },
                ],
            }],
            spans: HashMap::new(),
        };
        let diags = crate::core::check_unit(&unit).expect("core");
        assert!(
            !diags.is_empty(),
            "hand-written (call free p) must be a drop or a rejection, not a plain use"
        );
    }
}
