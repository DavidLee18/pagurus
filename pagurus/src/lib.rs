//! pagurus: verified ownership diagnostics for a small C subset.
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
}
