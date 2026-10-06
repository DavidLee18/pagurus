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
fn pass_free_null_constant_is_clean() {
    let diags = check(&fixture("pass", "free_null.c"));
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

fn ownership_crash(d: &pagurus::Diagnostic) -> bool {
    matches!(
        d.kind,
        DiagnosticKind::UseAfterMove | DiagnosticKind::UseAfterFree | DiagnosticKind::DoubleFree
    )
}

#[test]
fn fail_while_cond_consume() {
    let path = fixture("fail", "while_cond_consume.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| ownership_crash(d))
        .expect("expected ownership error: while must evaluate consume(p) on exit");
    let text = normalize(&hit.to_string(), &path);
    assert_golden("while_cond_consume.txt", &text);
}

#[test]
fn fail_for_cond_consume() {
    let path = fixture("fail", "for_cond_consume.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| ownership_crash(d))
        .expect("expected ownership error: for must evaluate consume(p) on exit");
    let text = normalize(&hit.to_string(), &path);
    assert_golden("for_cond_consume.txt", &text);
}

#[test]
fn fail_for_step_free() {
    let path = fixture("fail", "for_step_free.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| ownership_crash(d))
        .expect("expected ownership error after for-step free");
    let text = normalize(&hit.to_string(), &path);
    assert_golden("for_step_free.txt", &text);
}

#[test]
fn fail_dowhile_control() {
    let path = fixture("fail", "dowhile_control.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| ownership_crash(d))
        .expect("expected ownership error on do-while consume");
    let text = normalize(&hit.to_string(), &path);
    assert_golden("dowhile_control.txt", &text);
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

#[test]
fn fail_free_null_identifier_is_rejected() {
    let diags = check(&fixture("fail", "free_null_ident.c"));
    assert!(
        !diags.is_empty(),
        "expected conservative rejection of free(NULL) as an identifier"
    );
}

/// Programs from the pg-cex2 adversarial suite that must stay accepted.
const CEX2_PASS: &[&str] = &[
    "safe_dowhile_use.c",
    "safe_for_use.c",
    "safe_nested_loops.c",
    "safe_while_int.c",
    "safe_while_ptr_use.c",
    "safe_while_realloc.c",
];

/// Programs from the pg-cex2 suite that must be rejected (false accepts,
/// already-rejected bugs, and conservative false rejects such as
/// `return_mid_loop_safe` / `sc_and_consume_safe`).
const CEX2_FAIL: &[&str] = &[
    "break_stmt.c",
    "comma_cond.c",
    "comma_for_header.c",
    "cond_assign_consume.c",
    "continue_for.c",
    "elseif_consume.c",
    "for_empty_cond_return.c",
    "for_empty_init_cond_df.c",
    "for_empty_step_df.c",
    "goto_stmt.c",
    "if_noelse_consume.c",
    "nested_for_inner_cond.c",
    "nested_inner_cond.c",
    "nested_outer_cond.c",
    "ptr_compound_alias.c",
    "ptr_increment_free.c",
    "return_consume_df.c",
    "return_mid_loop_safe.c",
    "sc_and_assign_move.c",
    "sc_and_consume_safe.c",
    "sc_and_reinit.c",
    "sc_decl_reinit.c",
    "sc_or_consume_df.c",
    "sc_or_reinit.c",
    "sc_while_reinit.c",
    "switch_stmt.c",
    "ternary_consume.c",
    "tu_malloc.c",
];

#[test]
fn cex2_safe_programs_are_accepted() {
    for name in CEX2_PASS {
        let diags = check(&fixture("pass", name));
        assert!(
            diags.is_empty(),
            "{name} must stay accepted, got {diags:?}"
        );
    }
}

#[test]
fn cex2_false_accepts_and_rejects_are_rejected() {
    for name in CEX2_FAIL {
        let diags = check(&fixture("fail", name));
        assert!(
            !diags.is_empty(),
            "{name} must be rejected, got a clean verdict"
        );
    }
}
