//! dep_graph — Generate a Graphviz DOT dependency graph for LubySequence theorems.
//!
//! Usage:
//!   dep_graph [--output graph.dot] [--dir LubySequence]
//!
//! Each node represents a theorem colored by its source file.
//! Directed edges indicate that one declaration's proof body references another.
//!
//! Run `dot -Tpdf graph.dot -o graph.pdf` to render the graph.

use {
    clap::Parser,
    std::{
        collections::{HashMap, HashSet},
        fs,
        io::{self, Write},
        path::{Path, PathBuf},
    },
    winnow::{
        ascii::{multispace1, space1},
        combinator::{alt, opt, preceded},
        error::ContextError,
        token::{any, take_while},
        Parser as WinnowParser,
    },
};

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

/// Generate a Graphviz DOT dependency graph for LubySequence theorems.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Directory containing .lean source files
    #[arg(long, default_value = "LubySequence")]
    dir: PathBuf,

    /// Output DOT file path
    #[arg(long, default_value = "graph.dot")]
    output: PathBuf,
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Fill colors per source file (Graphviz HTML color strings).
fn file_color(filename: &str) -> &'static str {
    match filename {
        "Size.lean" => "#AED6F1",            // light blue
        "Basic.lean" => "#A9DFBF",           // light green
        "TrailingZeros.lean" => "#F9E79F",   // light yellow
        "SegmentSequence.lean" => "#F5CBA7", // light orange
        "Equivalence.lean" => "#D7BDE2",     // light purple
        _ => "#DDDDDD",
    }
}

// ---------------------------------------------------------------------------
// Character predicates for Lean identifiers
// ---------------------------------------------------------------------------

/// Returns true for characters that may appear in a Lean identifier.
///
/// Lean 4 identifiers consist of:
/// - ASCII word characters: `[A-Za-z0-9_]`
/// - ASCII apostrophe `'`
/// - Unicode subscript digits  ₀–₉  (U+2080–U+2089)
/// - Unicode subscript u       ᵤ    (U+1D64)
/// - Unicode superscript chars ⁰–⁹  (U+2070–U+2079, U+00B2–U+00B3, U+00B9)
/// - Greek and other math letters commonly used in Lean/Mathlib proofs
fn is_lean_ident_char(c: char) -> bool {
    matches!(c,
        'A'..='Z'
        | 'a'..='z'
        | '0'..='9'
        | '_'
        | '\''
        // Subscript digits ₀–₉
        | '\u{2080}'..='\u{2089}'
        // Subscript u  ᵤ
        | '\u{1D64}'
        // Superscript 2–3
        | '\u{00B2}'..='\u{00B3}'
        // Superscript 1
        | '\u{00B9}'
        // Superscript 0, 4–9
        | '\u{2070}'..='\u{2079}'
        // Subscript block (broad)
        | '\u{2080}'..='\u{209F}'
        // Greek lowercase α–ω
        | '\u{03B1}'..='\u{03C9}'
        // Greek uppercase Α–Ω
        | '\u{0391}'..='\u{03A9}'
        // Letterlike symbols (ℕ, ℤ, ℝ, etc.)
        | '\u{2100}'..='\u{214F}'
    )
}

/// Returns true for characters that are valid as the *first* character of a
/// Lean identifier (same as `is_lean_ident_char` but excludes digits and `'`).
fn is_lean_ident_start(c: char) -> bool {
    is_lean_ident_char(c) && !matches!(c, '0'..='9' | '\'')
}

// ---------------------------------------------------------------------------
// Winnow parsers
// ---------------------------------------------------------------------------

/// Parse an optional visibility modifier: `public`, `private`, or `protected`.
fn visibility(input: &mut &str) -> winnow::ModalResult<()> {
    opt(alt((
        preceded("public", multispace1),
        preceded("private", multispace1),
        preceded("protected", multispace1),
    )))
    .void()
    .parse_next(input)
}

/// Parse a Lean identifier (one or more identifier characters starting with a
/// valid start character).  Returns the matched slice.
fn lean_ident<'s>(input: &mut &'s str) -> winnow::ModalResult<&'s str> {
    // First char must be a valid start character
    let start = *input;
    let first: char = any::<&str, ContextError>
        .verify(|c: &char| is_lean_ident_start(*c))
        .parse_next(input)?;
    // Rest: zero or more identifier continuation characters
    let rest = take_while(0.., is_lean_ident_char).parse_next(input)?;
    // Reconstruct the full slice from the original input position
    let len = first.len_utf8() + rest.len();
    Ok(&start[..len])
}

/// Parse a declaration line of the form:
///   `[visibility] theorem <ident>`
/// Returns the identifier name if matched, or fails.
fn decl_line_name<'s>(input: &mut &'s str) -> winnow::ModalResult<&'s str> {
    visibility.parse_next(input)?;
    "theorem".parse_next(input)?;
    space1.parse_next(input)?;
    lean_ident.parse_next(input)
}

/// Returns `true` if the given (already trimmed) line is a `theorem` declaration
/// and yields the declaration name.
fn parse_decl_name(line: &str) -> Option<&str> {
    let mut input = line;
    decl_line_name.parse_next(&mut input).ok()
}

/// Returns `true` if the given (already trimmed) line starts with `@[`
/// (a Lean attribute annotation).
fn is_attr_line(line: &str) -> bool {
    line.starts_with("@[")
}

// ---------------------------------------------------------------------------
// Body token scanner — replaces find_dependencies
// ---------------------------------------------------------------------------

/// Scan `body` for occurrences of `needle` that are **not** surrounded by
/// identifier characters on either side, and are **not** immediately followed
/// by `.` (which would make it a qualified name prefix rather than a reference
/// to `needle` itself).
///
/// This is a pure character-walk — no regex engine involved.
fn body_contains_ref(body: &str, needle: &str) -> bool {
    if needle.is_empty() {
        return false;
    }
    let needle_bytes = needle.as_bytes();
    let body_bytes = body.as_bytes();
    let body_chars: Vec<char> = body.chars().collect();
    let needle_chars: Vec<char> = needle.chars().collect();
    let nlen = needle_chars.len();
    let blen = body_chars.len();

    // Build a byte-offset -> char-index map so we can check surroundings.
    // We iterate char-by-char for correctness with multibyte characters.
    let mut ci = 0usize; // char index
    let mut bi = 0usize; // byte index into body

    while bi + needle_bytes.len() <= body.len() {
        // Fast check: does the byte slice match?
        if &body_bytes[bi..bi + needle_bytes.len()] == needle_bytes {
            // Check character *before* the match
            let prev_ok = ci == 0 || !is_lean_ident_char(body_chars[ci - 1]);

            // Check character *after* the match
            let after_ci = ci + nlen;
            let after_ok = after_ci >= blen
                || (!is_lean_ident_char(body_chars[after_ci]) && body_chars[after_ci] != '.');

            if prev_ok && after_ok {
                return true;
            }
        }
        // Advance by one char
        bi += body_chars[ci].len_utf8();
        ci += 1;
    }
    false
}

// ---------------------------------------------------------------------------
// Pass 1 — collect declarations
// ---------------------------------------------------------------------------

/// Collect all declaration names from every `*.lean` file in `lean_dir`.
/// Returns a map `name -> filename (basename)`.
fn collect_declarations(lean_dir: &Path) -> HashMap<String, String> {
    let mut decl_to_file: HashMap<String, String> = HashMap::new();

    let mut entries = lean_files(lean_dir);
    entries.sort();

    for path in &entries {
        let fname = path.file_name().unwrap().to_string_lossy().into_owned();
        let text = fs::read_to_string(path).expect("read lean file");
        for line in text.lines() {
            let stripped = line.trim();
            if is_attr_line(stripped) {
                continue;
            }
            if let Some(name) = parse_decl_name(stripped) {
                decl_to_file.insert(name.to_owned(), fname.clone());
            }
        }
    }

    decl_to_file
}

// ---------------------------------------------------------------------------
// Proof-body extraction
// ---------------------------------------------------------------------------

/// Extract the proof body for the declaration at line index `start` (0-based).
/// Stops before the next top-level declaration or its preamble (doc comment /
/// attribute annotation).
fn extract_proof_body(lines: &[&str], start: usize) -> String {
    let mut result: Vec<&str> = vec![lines[start]];
    let mut pending: Vec<&str> = Vec::new();

    for &line in lines.iter().skip(start + 1) {
        let stripped = line.trim();

        // Doc comment boundary `/--`
        if stripped.starts_with("/--") {
            break;
        }
        // Attribute annotation — may precede a declaration; hold in pending
        if is_attr_line(stripped) {
            pending.push(line);
            continue;
        }
        // Next declaration boundary
        if parse_decl_name(stripped).is_some() {
            break;
        }
        // Flush pending attribute lines that did NOT precede a declaration
        result.extend_from_slice(&pending);
        pending.clear();
        result.push(line);
    }

    result.join("\n")
}

// ---------------------------------------------------------------------------
// Dependency search
// ---------------------------------------------------------------------------

/// Find all known declaration names referenced in `body`, excluding `own_name`.
fn find_dependencies<'a>(
    body: &str,
    all_names: &'a HashSet<String>,
    own_name: &str,
) -> HashSet<&'a str> {
    let mut deps = HashSet::new();
    for name in all_names {
        if name == own_name {
            continue;
        }
        if body_contains_ref(body, name) {
            deps.insert(name.as_str());
        }
    }
    deps
}

// ---------------------------------------------------------------------------
// Graph construction
// ---------------------------------------------------------------------------

/// Build the full dependency graph.
///
/// Returns `(decl_to_file, edges)` where `edges[name]` is the set of
/// declaration names that `name` depends on.
fn build_graph(lean_dir: &Path) -> (HashMap<String, String>, HashMap<String, HashSet<String>>) {
    let decl_to_file = collect_declarations(lean_dir);
    let all_names: HashSet<String> = decl_to_file.keys().cloned().collect();
    let mut edges: HashMap<String, HashSet<String>> = all_names
        .iter()
        .map(|n| (n.clone(), HashSet::new()))
        .collect();

    let mut entries = lean_files(lean_dir);
    entries.sort();

    for path in &entries {
        let text = fs::read_to_string(path).expect("read lean file");
        let lines: Vec<&str> = text.lines().collect();

        for (i, line) in lines.iter().enumerate() {
            let stripped = line.trim();
            if is_attr_line(stripped) {
                continue;
            }
            if let Some(name) = parse_decl_name(stripped) {
                let body = extract_proof_body(&lines, i);
                let deps = find_dependencies(&body, &all_names, name);
                edges
                    .entry(name.to_owned())
                    .or_default()
                    .extend(deps.into_iter().map(str::to_owned));
            }
        }
    }

    (decl_to_file, edges)
}

// ---------------------------------------------------------------------------
// DOT identifier sanitization
// ---------------------------------------------------------------------------

/// Convert a Lean declaration name into a valid DOT node identifier.
fn sanitize_dot_id(name: &str) -> String {
    let mut s = String::with_capacity(name.len() * 2);
    for ch in name.chars() {
        let replacement: Option<&str> = match ch {
            // Subscript digits ₀–₉
            '\u{2080}' => Some("0"),
            '\u{2081}' => Some("1"),
            '\u{2082}' => Some("2"),
            '\u{2083}' => Some("3"),
            '\u{2084}' => Some("4"),
            '\u{2085}' => Some("5"),
            '\u{2086}' => Some("6"),
            '\u{2087}' => Some("7"),
            '\u{2088}' => Some("8"),
            '\u{2089}' => Some("9"),
            // Superscript digits ⁰–⁹
            '\u{2070}' => Some("0"),
            '\u{00B9}' => Some("1"),
            '\u{00B2}' => Some("2"),
            '\u{00B3}' => Some("3"),
            '\u{2074}' => Some("4"),
            '\u{2075}' => Some("5"),
            '\u{2076}' => Some("6"),
            '\u{2077}' => Some("7"),
            '\u{2078}' => Some("8"),
            '\u{2079}' => Some("9"),
            // Apostrophe / prime
            '\'' => Some("_prime"),
            _ => None,
        };
        match replacement {
            Some(r) => s.push_str(r),
            None => {
                if ch.is_ascii_alphanumeric() || ch == '_' {
                    s.push(ch);
                } else {
                    s.push('_');
                }
            }
        }
    }
    s
}

// ---------------------------------------------------------------------------
// DOT output
// ---------------------------------------------------------------------------

/// Write the dependency graph in Graphviz DOT format to `output_path`.
fn write_dot(
    decl_to_file: &HashMap<String, String>,
    edges: &HashMap<String, HashSet<String>>,
    output_path: &Path,
) -> io::Result<()> {
    let mut all_names: Vec<&String> = decl_to_file.keys().collect();
    all_names.sort();

    let mut out = fs::File::create(output_path)?;

    writeln!(out, "digraph LubyDependencies {{")?;
    writeln!(out, "  rankdir=TB;")?;
    writeln!(
        out,
        r#"  node [shape=box, style=filled, fontname="Helvetica", fontsize=9];"#
    )?;
    writeln!(out, "  edge [arrowsize=0.6];")?;
    writeln!(out)?;

    // the table of the nodes which have inflax.
    let nodes_with_inflax = edges.values().flatten().collect::<HashSet<_>>();

    // Nodes
    for name in &all_names {
        // Skip nodes that have no entry in the edges map
        if !edges.contains_key(*name) || !nodes_with_inflax.contains(name) {
            continue;
        }
        let fname = &decl_to_file[*name];
        let node_id = sanitize_dot_id(name);
        let color = file_color(fname);
        writeln!(out, r#"  {node_id} [label="{name}", fillcolor="{color}"];"#)?;
    }
    writeln!(out)?;

    // Edges — dst -> src means src depends on dst
    for src_name in &all_names {
        let src_id = sanitize_dot_id(src_name);
        if let Some(deps) = edges.get(*src_name) {
            let mut sorted_deps: Vec<&String> = deps.iter().collect();
            sorted_deps.sort();
            for dst_name in sorted_deps {
                if decl_to_file.contains_key(dst_name) {
                    let dst_id = sanitize_dot_id(dst_name);
                    writeln!(out, "  {dst_id} -> {src_id};")?;
                }
            }
        }
    }

    writeln!(out, "}}")?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Utilities
// ---------------------------------------------------------------------------

/// Collect all `*.lean` files directly inside `dir` (non-recursive).
fn lean_files(dir: &Path) -> Vec<PathBuf> {
    let rd = match fs::read_dir(dir) {
        Ok(rd) => rd,
        Err(e) => {
            eprintln!("Error reading directory {}: {}", dir.display(), e);
            return Vec::new();
        }
    };
    rd.filter_map(|entry| {
        let entry = entry.ok()?;
        let path = entry.path();
        if path.is_file() && path.extension().is_some_and(|e| e == "lean") {
            Some(path)
        } else {
            None
        }
    })
    .collect()
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn main() {
    let args = Args::parse();

    if !args.dir.is_dir() {
        eprintln!("Error: directory not found: {}", args.dir.display());
        std::process::exit(1);
    }

    let (decl_to_file, edges) = build_graph(&args.dir);

    let total_decls = decl_to_file.len();
    let total_files: HashSet<&String> = decl_to_file.values().collect();
    let total_edges: usize = edges.values().map(|v| v.len()).sum();

    println!(
        "Found {total_decls} declarations across {} files.",
        total_files.len()
    );
    println!("Found {total_edges} dependency edges.");

    if let Err(e) = write_dot(&decl_to_file, &edges, &args.output) {
        eprintln!("Error writing DOT file: {e}");
        std::process::exit(1);
    }

    println!("Written: {}", args.output.display());
    println!(
        "Render with: dot -Tpdf {} -o graph.pdf",
        args.output.display()
    );
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- lean_ident ---
    fn parse_ident(s: &str) -> winnow::ModalResult<&str> {
        let mut input = s;
        lean_ident.parse_next(&mut input)
    }

    #[test]
    fn test_lean_ident_ascii() {
        assert_eq!(parse_ident("foo_bar").unwrap(), "foo_bar");
    }

    #[test]
    fn test_lean_ident_prime() {
        assert_eq!(parse_ident("h'").unwrap(), "h'");
    }

    #[test]
    fn test_lean_ident_subscript() {
        // S₂  (S + U+2082)
        assert_eq!(parse_ident("S₂").unwrap(), "S₂");
    }

    #[test]
    fn test_lean_ident_rejects_digit_start() {
        assert!(parse_ident("1foo").is_err());
    }

    // --- parse_decl_name ---

    #[test]
    fn test_parse_decl_name_simple() {
        assert_eq!(parse_decl_name("theorem foo"), Some("foo"));
    }

    #[test]
    fn test_parse_decl_name_private() {
        assert_eq!(parse_decl_name("private theorem bar"), Some("bar"));
    }

    #[test]
    fn test_parse_decl_name_public() {
        assert_eq!(parse_decl_name("public theorem baz'"), Some("baz'"));
    }

    #[test]
    fn test_parse_decl_name_not_theorem() {
        assert_eq!(parse_decl_name("def foo"), None);
    }

    #[test]
    fn test_parse_decl_name_empty() {
        assert_eq!(parse_decl_name(""), None);
    }

    // --- is_attr_line ---

    #[test]
    fn test_attr_line_simp() {
        assert!(is_attr_line("@[simp]"));
    }

    #[test]
    fn test_attr_line_not_attr() {
        assert!(!is_attr_line("theorem foo"));
    }

    // --- body_contains_ref ---

    #[test]
    fn test_body_contains_ref_simple() {
        assert!(body_contains_ref("exact foo", "foo"));
    }

    #[test]
    fn test_body_contains_ref_not_prefix() {
        // "foobar" should NOT match needle "foo"
        assert!(!body_contains_ref("exact foobar", "foo"));
    }

    #[test]
    fn test_body_contains_ref_not_suffix() {
        // "myfoo" should NOT match needle "foo"
        assert!(!body_contains_ref("exact myfoo", "foo"));
    }

    #[test]
    fn test_body_contains_ref_qualified_name() {
        // "foo.bar" should NOT match bare needle "foo" (followed by '.')
        assert!(!body_contains_ref("exact foo.bar", "foo"));
    }

    #[test]
    fn test_body_contains_ref_at_start() {
        assert!(body_contains_ref("foo ▸ rfl", "foo"));
    }

    #[test]
    fn test_body_contains_ref_unicode_name() {
        assert!(body_contains_ref("apply S₂_ge_two", "S₂_ge_two"));
    }

    #[test]
    fn test_body_contains_ref_unicode_not_prefix() {
        assert!(!body_contains_ref("apply S₂_ge_two_extra", "S₂_ge_two"));
    }

    #[test]
    fn test_body_contains_ref_self_excluded_by_caller() {
        // body_contains_ref itself does NOT exclude own_name; that's done by
        // find_dependencies. Confirm it matches itself when called directly.
        assert!(body_contains_ref("rw [luby_seq]", "luby_seq"));
    }

    // --- sanitize_dot_id ---

    #[test]
    fn test_sanitize_ascii() {
        assert_eq!(sanitize_dot_id("foo_bar"), "foo_bar");
    }

    #[test]
    fn test_sanitize_prime() {
        assert_eq!(sanitize_dot_id("h'"), "h_prime");
    }

    #[test]
    fn test_sanitize_subscript() {
        assert_eq!(sanitize_dot_id("S₂"), "S2");
    }

    #[test]
    fn test_sanitize_superscript() {
        assert_eq!(sanitize_dot_id("x²"), "x2");
    }
}
