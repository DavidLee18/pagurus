use std::path::{Path, PathBuf};

use pagurus::{check_file, DiagnosticKind};

fn fixtures_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("tests")
        .join("fixtures")
}

fn goldens_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("tests")
        .join("golden")
}

fn fixture(kind: &str, name: &str) -> PathBuf {
    fixtures_root().join(kind).join(name)
}

fn check(path: &Path) -> Vec<pagurus::Diagnostic> {
    check_file(path).unwrap_or_else(|e| panic!("failed to analyze {}: {e}", path.display()))
}

fn normalize(text: &str, path: &Path) -> String {
    let display = path.display().to_string();
    let name = path.file_name().unwrap().to_string_lossy();
    text.replace(&display, &name)
}

fn assert_golden(name: &str, rendered: &str) {
    let path = goldens_root().join(name);
    if std::env::var("UPDATE_GOLDENS").ok().as_deref() == Some("1") {
        std::fs::create_dir_all(goldens_root()).unwrap();
        std::fs::write(&path, rendered).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&path).unwrap_or_else(|_| {
        panic!(
            "missing golden {} — run UPDATE_GOLDENS=1 cargo test to create it\n--- rendered ---\n{rendered}",
            path.display()
        )
    });
    assert_eq!(
        expected, rendered,
        "golden mismatch for {name}; run UPDATE_GOLDENS=1 cargo test to update"
    );
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
fn pass_nested_shadow_is_clean() {
    let diags = check(&fixture("pass", "nested_shadow.c"));
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
}

#[test]
fn pass_loop_borrow_is_clean() {
    let diags = check(&fixture("pass", "loop_borrow.c"));
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
}

#[test]
fn pass_pointer_param_borrow_is_clean() {
    let diags = check(&fixture("pass", "pointer_param_borrow.c"));
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
    let text = normalize(&hit.to_string(), &path);
    assert!(text.contains("use of moved value `p`"));
    assert!(text.contains("used here after move"));
    assert!(text.contains("value moved here"));
    assert!(text.contains("help:"));
    assert_golden("use_after_move.txt", &text);
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
    let text = normalize(&hit.to_string(), &path);
    assert!(text.contains("double free of `p`"));
    assert!(text.contains("first freed here"));
    assert_golden("double_free.txt", &text);
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
    let text = normalize(&hit.to_string(), &path);
    assert!(text.contains("use of freed value `p`"));
    assert_golden("use_after_free.txt", &text);
}

#[test]
fn fail_chained_assign_is_use_after_move() {
    let diags = check(&fixture("fail", "chained_assign.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::UseAfterMove),
        "expected use-after-move on chained assign, got {diags:?}"
    );
}

#[test]
fn fail_if_join_use_after_free() {
    let diags = check(&fixture("fail", "if_join_use_after_free.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::UseAfterFree),
        "expected use-after-free after if-join, got {diags:?}"
    );
}

#[test]
fn fail_for_init_double_free() {
    let diags = check(&fixture("fail", "for_init_double_free.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::DoubleFree),
        "expected double-free in for-init, got {diags:?}"
    );
}

#[test]
fn fail_loop_free_then_use() {
    let diags = check(&fixture("fail", "loop_free_then_use.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::UseAfterFree
            || d.kind == DiagnosticKind::DoubleFree
            || d.kind == DiagnosticKind::Unproven),
        "expected a loop ownership error, got {diags:?}"
    );
}

#[test]
fn fail_pointer_param_consume() {
    let diags = check(&fixture("fail", "pointer_param_consume.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::UseAfterMove),
        "expected use-after-move after consuming call, got {diags:?}"
    );
}

#[test]
fn fail_unsupported_goto() {
    let path = fixture("fail", "unsupported_goto.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| d.kind == DiagnosticKind::Unsupported)
        .expect("expected unsupported diagnostic");
    let text = normalize(&hit.to_string(), &path);
    assert!(text.contains("unsupported construct"));
    assert!(text.contains("goto"));
    assert_golden("unsupported_goto.txt", &text);
}

#[test]
fn fail_unsupported_pointer_arith() {
    let diags = check(&fixture("fail", "unsupported_pointer_arith.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::Unsupported),
        "expected unsupported pointer arithmetic, got {diags:?}"
    );
}

#[test]
fn fail_opaque_prototype_is_unsupported() {
    let diags = check(&fixture("fail", "opaque_call.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::Unsupported),
        "expected unsupported opaque call, got {diags:?}"
    );
}
