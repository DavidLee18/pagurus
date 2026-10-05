//! pagurus: static ownership diagnostics for a small C subset.

mod analyze;
mod diag;
mod hir;
mod parse;

pub use diag::{Diagnostic, DiagnosticKind, Note, SrcSpan};
pub use hir::Unit;
pub use parse::ParseError;

use std::path::Path;

use crate::analyze::analyze_unit;
use crate::parse::{parse_file as parse_path, parse_source};

/// Parse and analyze C source text.
pub fn check_source(filename: &str, source: &str) -> Result<Vec<Diagnostic>, ParseError> {
    let unit = parse_source(filename, source)?;
    Ok(analyze_unit(&unit))
}

/// Parse and analyze a C source file on disk.
pub fn check_file<P: AsRef<Path>>(path: P) -> Result<Vec<Diagnostic>, ParseError> {
    let path = path.as_ref();
    let unit = parse_path(path)?;
    Ok(analyze_unit(&unit))
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
    }
}
