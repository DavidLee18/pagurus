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
fn pass_free_null_identifier_is_clean() {
    let diags = check(&fixture("pass", "free_null_ident.c"));
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
}

#[test]
fn pass_known_null_free_is_clean() {
    for name in [
        "null_after_free.c",
        "assign_null_then_free.c",
        "free_null_twice.c",
    ] {
        let diags = check(&fixture("pass", name));
        assert!(diags.is_empty(), "{name} must be accepted, got {diags:?}");
    }
}

#[test]
fn pass_return_ends_the_path() {
    for name in [
        "early_return_free.c",
        "dead_free_after_return.c",
        "return_mid_loop_safe.c",
        "for_empty_cond_return.c",
    ] {
        let diags = check(&fixture("pass", name));
        assert!(diags.is_empty(), "{name} must be accepted, got {diags:?}");
    }
}

#[test]
fn pass_realloc_ok_is_clean() {
    let diags = check(&fixture("pass", "realloc_ok.c"));
    assert!(diags.is_empty(), "unexpected diagnostics: {diags:?}");
}

#[test]
fn pass_per_arg_consume_is_clean() {
    for name in [
        "wrap_free_first.c",
        "wrap_free_second.c",
        "wrap_free_middle.c",
    ] {
        let diags = check(&fixture("pass", name));
        assert!(diags.is_empty(), "{name} must be accepted, got {diags:?}");
    }
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
    assert!(text.contains("freed here after move"));
    assert!(text.contains("value moved here"));
    assert!(text.contains("help:"));
    assert!(text.contains("may be a double free"));
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
fn fail_consume2_same_names_the_argument() {
    let path = fixture("fail", "consume2_same.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| ownership_crash(d))
        .expect("expected ownership error on c2(p,p)");
    let text = normalize(&hit.to_string(), &path);
    assert!(
        text.contains("argument `p` is consumed by `c2`"),
        "diagnostic must name the consumed argument, got:\n{text}"
    );
}

#[test]
fn fail_wrap_free_first_df_stays_rejected() {
    for name in ["wrap_free_first_df.c", "wrap_free_first_uaf.c", "wrap_free_first_alias.c"] {
        let diags = check(&fixture("fail", name));
        assert!(
            !diags.is_empty(),
            "{name} must be rejected, got a clean verdict"
        );
    }
}

fn unique_span_ids(d: &pagurus::Diagnostic) -> bool {
    let mut keys = vec![(d.span.line, d.span.column, d.primary_label.as_str())];
    for n in &d.notes {
        keys.push((n.span.line, n.span.column, n.message.as_str()));
    }
    let mut sorted = keys.clone();
    sorted.sort();
    sorted.dedup();
    sorted.len() == keys.len()
}

#[test]
fn fail_id_alias_explains_possible_double_free() {
    let path = fixture("fail", "id_alias.c");
    let diags = check(&path);
    let hit = diags.first().expect("id_alias must stay rejected");
    let text = normalize(&hit.to_string(), &path);
    assert!(
        text.contains("double free") || text.contains("id"),
        "should hint at a double free / identity alias, got:\n{text}"
    );
    assert!(unique_span_ids(hit), "duplicate node labels:\n{text}");
    assert_golden("id_alias.txt", &text);
}

#[test]
fn fail_id_alias_only_q_explains_untracked_call() {
    let path = fixture("fail", "id_alias_only_q.c");
    let diags = check(&path);
    let hit = diags.first().expect("id_alias_only_q must stay rejected");
    let text = normalize(&hit.to_string(), &path);
    assert!(
        text.contains("call") && text.contains("double free"),
        "should say ownership is untracked through a call, got:\n{text}"
    );
    assert!(unique_span_ids(hit), "duplicate node labels:\n{text}");
    assert_golden("id_alias_only_q.txt", &text);
}

#[test]
fn fail_cast_launder_explains_possible_double_free() {
    for name in ["cast_launder_int.c", "cast_uintptr_alias.c"] {
        let path = fixture("fail", name);
        let diags = check(&path);
        let hit = diags
            .first()
            .unwrap_or_else(|| panic!("{name} must stay rejected"));
        let text = normalize(&hit.to_string(), &path);
        assert!(
            !diags.is_empty(),
            "{name} must stay rejected"
        );
        assert!(
            text.contains("cast") || text.contains("integer") || text.contains("double free"),
            "{name} should hint at laundering / double free, got:\n{text}"
        );
        assert!(unique_span_ids(hit), "{name} duplicate node labels:\n{text}");
        if name == "cast_launder_int.c" {
            assert_golden("cast_launder_int.txt", &text);
        }
    }
}

#[test]
fn fail_realloc_df_explains_consumed_pointer() {
    let path = fixture("fail", "realloc_df.c");
    let diags = check(&path);
    let hit = diags
        .iter()
        .find(|d| ownership_crash(d) || d.kind == DiagnosticKind::Unproven)
        .expect("realloc_df must stay rejected");
    let text = normalize(&hit.to_string(), &path);
    assert!(
        text.contains("double free") || text.contains("realloc") || text.contains("moved"),
        "should explain realloc consumed p, got:\n{text}"
    );
    assert!(unique_span_ids(hit), "duplicate node labels:\n{text}");
    assert_golden("realloc_df.txt", &text);
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
fn fail_else_return_then_df() {
    let diags = check(&fixture("fail", "else_return_then_df.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::DoubleFree
            || d.kind == DiagnosticKind::UseAfterFree),
        "expected double-free after a non-returning then-branch, got {diags:?}"
    );
}

#[test]
fn fail_wrap_return_df_is_not_treated_as_null() {
    let diags = check(&fixture("fail", "wrap_return_df.c"));
    assert!(
        !diags.is_empty(),
        "a malloc-returning wrapper must not be modelled as known-null (would hide a double free)"
    );
}

#[test]
fn fail_realloc_result_df() {
    let diags = check(&fixture("fail", "realloc_result_df.c"));
    assert!(
        diags.iter().any(|d| d.kind == DiagnosticKind::DoubleFree),
        "expected double-free of realloc result, got {diags:?}"
    );
}

#[test]
fn fail_tu_realloc_is_not_synthetic() {
    let diags = check(&fixture("fail", "tu_realloc.c"));
    assert!(
        !diags.is_empty(),
        "a realloc defined in this TU must not be the synthetic allocator"
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
    "return_mid_loop_safe.c",
    "for_empty_cond_return.c",
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

/// pg-cex3 programmes that pagurus accepted at c3de693 (`pag_rc=0`).
const CEX3_PASS: &[&str] = &[
    "cast_lhs_assign.c",
    "two_sinks.c",
    "null_after_free.c",
    "realloc_ok.c",
    "wrap_free_first.c",
];

/// pg-cex3 programmes rejected by the checker at c3de693 (`pag_rc=1`).
const CEX3_FAIL: &[&str] = &[
    "calloc_df.c",
    "cast_arith_hidden.c",
    "cast_char_void.c",
    "cast_launder_int.c",
    "cast_long_plus0.c",
    "cast_long_roundtrip.c",
    "cast_uintptr_alias.c",
    "consume2_same.c",
    "fnptr_free.c",
    "fnptr_wrapper.c",
    "id_alias.c",
    "id_alias_only_q.c",
    "if_guard_free.c",
    "mutual_rec.c",
    "param_consume_unseen.c",
    "pp_addr_consume.c",
    "pp_deref_free.c",
    "realloc_df.c",
    "return_p_alias.c",
    "strdup_df.c",
    "unary_addr.c",
    "variadic_consume.c",
    "wrap_cond_free.c",
    "wrap_free_first_df.c",
    "wrap_free_first_alias.c",
    "wrap_free_first_uaf.c",
    "wrap_maybe_use.c",
    "wrap_move_then_free.c",
    "wrap_myfree_twice.c",
    "wrap_of_wrapper.c",
];

#[test]
fn cex3_accepted_programs_stay_accepted() {
    for name in CEX3_PASS {
        let diags = check(&fixture("pass", name));
        assert!(
            diags.is_empty(),
            "{name} must stay accepted (RESULTS.txt pag_rc=0), got {diags:?}"
        );
    }
}

#[test]
fn cex3_rejected_programs_stay_rejected() {
    for name in CEX3_FAIL {
        let diags = check(&fixture("fail", name));
        assert!(
            !diags.is_empty(),
            "{name} must stay rejected (RESULTS.txt pag_rc=1), got a clean verdict"
        );
    }
}

#[test]
fn cex3_stmt_expr_stays_a_parse_failure() {
    let path = fixture("fail", "stmt_expr.c");
    let err = check_file(&path).expect_err(
        "RESULTS.txt pag_rc=2: GNU statement-expression must fail to parse, not reach the checker",
    );
    assert!(
        err.to_string().contains("failed to parse"),
        "expected a parse error, got {err}"
    );
}

/// pg-cex4 programmes that must be rejected. `a1`–`a4` are the
/// literal-as-null soundness regression; the rest are sound rejects
/// from that suite's RESULTS.txt.
const CEX4_FAIL: &[&str] = &[
    "a1_lit1.c",
    "a2_free_then_lit.c",
    "a3_litnocast.c",
    "a4_strlit.c",
    "c1_ifnull_df.c",
    "c2_join_df.c",
    "r1_realloc_old_df.c",
    "r2_realloc_self_df.c",
    "ret1_elsepath_df.c",
];

#[test]
fn cex4_literal_null_false_accepts_are_rejected() {
    for name in [
        "a1_lit1.c",
        "a2_free_then_lit.c",
        "a3_litnocast.c",
        "a4_strlit.c",
    ] {
        let diags = check(&fixture("fail", name));
        assert!(
            !diags.is_empty(),
            "{name} must be rejected (non-null literal is not ANull), got a clean verdict"
        );
    }
}

#[test]
fn cex4_rejected_programs_stay_rejected() {
    for name in CEX4_FAIL {
        let diags = check(&fixture("fail", name));
        assert!(
            !diags.is_empty(),
            "{name} must stay rejected (RESULTS.txt pag_rc=1), got a clean verdict"
        );
    }
}

/// pg-cex4 / PR #11 programmes: per-arg consume summaries correctly reject.
const CEX4_PR11_FAIL: &[&str] = &[
    "m1_move_local_free.c",
    "m2_direct.c",
    "m3_cond_df.c",
    "m4_chain.c",
    "m5_dup_arg.c",
    "m6_second_param.c",
    "m7_uaf.c",
    "m8_realloc_param.c",
    "m9_recur.c",
    "m10_mutual.c",
    "m11_reassign.c",
];

#[test]
fn cex4_per_arg_consume_programs_are_rejected() {
    for name in CEX4_PR11_FAIL {
        let diags = check(&fixture("fail", name));
        assert!(
            !diags.is_empty(),
            "{name} must stay rejected (RESULTS.txt pag_rc=1), got a clean verdict"
        );
    }
}
