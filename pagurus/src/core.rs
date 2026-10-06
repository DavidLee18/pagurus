//! Spawn the Idris `pagurus-core` executable. Rust never overrides its verdict.

use std::collections::HashMap;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;

use crate::diag::{Diagnostic, DiagnosticKind, Label, SrcSpan};
use crate::hir::Unit;
use crate::parse::ParseError;

#[derive(Debug, serde::Deserialize)]
struct CoreJson {
    verdict: String,
    #[serde(default)]
    diagnostics: Vec<CoreDiagJson>,
}

#[derive(Debug, serde::Deserialize)]
struct CoreDiagJson {
    code: String,
    message: String,
    primary: CoreLocJson,
    #[serde(default)]
    secondary: Vec<CoreLocJson>,
    #[serde(default)]
    help: String,
}

#[derive(Debug, serde::Deserialize)]
struct CoreLocJson {
    id: u32,
    label: String,
}

const CORE_MISSING: &str = "pagurus-core not found. Build it with Idris 2 0.8.0 \
(`cargo test --features build-core`, or `cd core && idris2 --build pagurus-core.ipkg`) \
and put `scheme` (Chez Scheme) on PATH, or set PAGURUS_CORE to the wrapper script. See README.";

pub fn check_unit(unit: &Unit) -> Result<Vec<Diagnostic>, ParseError> {
    let ir = crate::emit::emit_unit(unit);
    let core = core_path().ok_or_else(|| ParseError {
        message: CORE_MISSING.into(),
    })?;

    let mut tmp = tempfile::NamedTempFile::new().map_err(|e| ParseError {
        message: format!("cannot create IR temp file: {e}"),
    })?;
    tmp.write_all(ir.as_bytes()).map_err(|e| ParseError {
        message: format!("cannot write IR temp file: {e}"),
    })?;
    tmp.flush().map_err(|e| ParseError {
        message: format!("cannot write IR temp file: {e}"),
    })?;

    let output = Command::new(&core)
        .arg(tmp.path())
        .output()
        .map_err(|e| ParseError {
            message: format!(
                "failed to spawn pagurus-core ({}): {e}. \
The Idris 2 binary is a Chez Scheme wrapper; install `scheme` on PATH. {CORE_MISSING}",
                core.display()
            ),
        })?;
    drop(tmp);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let line = stdout.lines().last().unwrap_or("").trim();
    if line.is_empty() {
        let hint = if stderr.contains("scheme") || stderr.contains("chez") {
            " Chez Scheme (`scheme`) is required to run pagurus-core."
        } else {
            ""
        };
        return Ok(vec![unproven(
            &unit.file,
            format!("pagurus-core produced no verdict (stderr: {stderr}).{hint}"),
        )]);
    }

    let parsed: CoreJson = serde_json::from_str(line).map_err(|e| ParseError {
        message: format!("pagurus-core returned invalid JSON: {e}: {line}"),
    })?;

    // Acceptance comes only from the core. Anything other than an explicit
    // "safe" verdict is treated as a rejection.
    if parsed.verdict == "safe" {
        return Ok(Vec::new());
    }

    if parsed.diagnostics.is_empty() {
        return Ok(vec![unproven(
            &unit.file,
            "pagurus-core rejected this program without a diagnostic".into(),
        )]);
    }

    Ok(parsed
        .diagnostics
        .into_iter()
        .map(|d| render_diag(&unit.file, &unit.spans, d))
        .collect())
}

fn render_diag(file: &str, spans: &HashMap<u32, SrcSpan>, d: CoreDiagJson) -> Diagnostic {
    let span = spans
        .get(&d.primary.id)
        .cloned()
        .unwrap_or_else(|| SrcSpan::dummy(file));
    let notes = d
        .secondary
        .into_iter()
        .map(|s| Label {
            message: s.label.clone(),
            span: spans
                .get(&s.id)
                .cloned()
                .unwrap_or_else(|| SrcSpan::dummy(file)),
        })
        .collect();
    Diagnostic {
        kind: DiagnosticKind::from_code(&d.code),
        message: d.message,
        span,
        primary_label: d.primary.label,
        notes,
        help: d.help,
    }
}

fn unproven(file: &str, message: String) -> Diagnostic {
    Diagnostic {
        kind: DiagnosticKind::Unproven,
        message,
        span: SrcSpan::dummy(file),
        primary_label: "here".into(),
        notes: Vec::new(),
        help: "the Idris core did not accept this program".into(),
    }
}

fn core_path() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("PAGURUS_CORE") {
        let pb = PathBuf::from(p);
        if pb.exists() {
            return Some(pb);
        }
    }
    if let Some(built) = option_env!("PAGURUS_CORE_PATH") {
        let pb = PathBuf::from(built);
        if pb.exists() {
            return Some(pb);
        }
    }
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let candidate = dir.join("pagurus-core");
            if candidate.exists() {
                return Some(candidate);
            }
        }
    }
    which("pagurus-core")
}

fn which(name: &str) -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path) {
        let candidate = dir.join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}
