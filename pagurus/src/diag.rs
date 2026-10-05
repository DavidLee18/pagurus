//! Source locations and rustc/CORAL-style diagnostics.

use std::fmt;
use std::path::Path;

/// A 1-based file/line/column location with the originating source line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SrcSpan {
    pub file: String,
    pub line: u32,
    pub column: u32,
    pub snippet: String,
}

impl SrcSpan {
    pub fn from_offset(file: &str, source: &str, offset: usize) -> Self {
        let (line, column, snippet) = line_col_snippet(source, offset);
        Self {
            file: file.to_string(),
            line,
            column,
            snippet,
        }
    }

    pub fn dummy(file: &str) -> Self {
        Self {
            file: file.to_string(),
            line: 1,
            column: 1,
            snippet: String::new(),
        }
    }
}

/// Convert a byte offset into 1-based line/column and the text of that line.
pub fn line_col_snippet(source: &str, offset: usize) -> (u32, u32, String) {
    let offset = offset.min(source.len());
    let mut line = 1u32;
    let mut col = 1u32;
    let mut line_start = 0usize;
    for (i, ch) in source.char_indices() {
        if i >= offset {
            break;
        }
        if ch == '\n' {
            line += 1;
            col = 1;
            line_start = i + 1;
        } else {
            col += 1;
        }
    }
    let rest = source.get(line_start..).unwrap_or("");
    let snippet = rest.lines().next().unwrap_or("").to_string();
    (line, col, snippet)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticKind {
    UseAfterMove,
    UseAfterFree,
    DoubleFree,
    Unsupported,
    Unproven,
}

impl DiagnosticKind {
    pub fn code(self) -> &'static str {
        match self {
            DiagnosticKind::UseAfterMove => "use_after_move",
            DiagnosticKind::UseAfterFree => "use_after_free",
            DiagnosticKind::DoubleFree => "double_free",
            DiagnosticKind::Unsupported => "unsupported",
            DiagnosticKind::Unproven => "unproven_ownership",
        }
    }

    pub fn from_code(code: &str) -> Self {
        match code {
            "use_after_move" => DiagnosticKind::UseAfterMove,
            "use_after_free" => DiagnosticKind::UseAfterFree,
            "double_free" => DiagnosticKind::DoubleFree,
            "unsupported" => DiagnosticKind::Unsupported,
            _ => DiagnosticKind::Unproven,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Label {
    pub message: String,
    pub span: SrcSpan,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub kind: DiagnosticKind,
    pub message: String,
    pub span: SrcSpan,
    pub primary_label: String,
    pub notes: Vec<Label>,
    pub help: String,
}

impl fmt::Display for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "error[{}]: {}", self.kind.code(), self.message)?;
        write_span(f, &self.span, &self.primary_label)?;
        for note in &self.notes {
            writeln!(f, "note: {}", note.message)?;
            write_span(f, &note.span, &note.message)?;
        }
        if !self.help.is_empty() {
            writeln!(f, "help: {}", self.help)?;
        }
        Ok(())
    }
}

fn write_span(f: &mut fmt::Formatter<'_>, span: &SrcSpan, caret_label: &str) -> fmt::Result {
    writeln!(f, " --> {}:{}:{}", span.file, span.line, span.column)?;
    writeln!(f, "  |")?;
    writeln!(f, "{:>4} | {}", span.line, span.snippet)?;
    let caret_col = span.column.max(1) as usize;
    let pad = " ".repeat(caret_col.saturating_sub(1));
    writeln!(f, "     | {pad}^ {caret_label}")?;
    Ok(())
}

pub fn display_path(path: &Path) -> String {
    path.display().to_string()
}
