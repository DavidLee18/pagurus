use std::path::{Path, PathBuf};

use pagurus::{check_file, DiagnosticKind};

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("tests")
        .join("fixtures")
}

fn fixture(kind: &str, name: &str) -> PathBuf {
    fixtures_root().join(kind).join(name)
}

fn check(path: &Path) -> Vec<pagurus::Diagnostic> {
    check_file(path).unwrap_or_else(|e| panic!("failed to analyze {}: {e}", path.display()))
}

#[test]
fn pass_malloc_free_is_clean() {
    let diags = check(&fixture("pass", "malloc_free.c"));
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
}

#[test]
fn pass_copy_int_is_clean() {
    let diags = check(&fixture("pass", "copy_int.c"));
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
}

#[test]
fn pass_borrow_then_free_is_clean() {
    let diags = check(&fixture("pass", "borrow_then_free.c"));
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
}

#[test]
fn fail_use_after_move() {
    let path = fixture("fail", "use_after_move.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| d.kind == DiagnosticKind::UseAfterMove)
        .expect("expected use-after-move diagnostic");
    assert!(hit.span.file.contains("use_after_move.c"));
    assert!(
        hit.span.line >= 8,
        "line should point at free(p), got {}",
        hit.span.line
    );
    let text = hit.to_string();
    assert!(text.contains("use of moved value `p`"));
    assert!(text.contains("--> "));
}

#[test]
fn fail_double_free() {
    let path = fixture("fail", "double_free.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| d.kind == DiagnosticKind::DoubleFree)
        .expect("expected double-free diagnostic");
    assert!(hit.span.file.contains("double_free.c"));
    assert!(
        hit.span.line >= 8,
        "line should point at the second free, got {}",
        hit.span.line
    );
    let text = hit.to_string();
    assert!(text.contains("double free of `p`"));
    assert!(text.contains("was freed here"));
}

#[test]
fn fail_use_after_free() {
    let path = fixture("fail", "use_after_free.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| d.kind == DiagnosticKind::UseAfterFree)
        .expect("expected use-after-free diagnostic");
    assert!(hit.span.file.contains("use_after_free.c"));
    assert!(hit.span.line >= 9);
    assert!(hit.to_string().contains("use of freed value `p`"));
}
