#!/usr/bin/env python3
"""
parse_theorems.py - Generate a Graphviz DOT dependency graph for LubySequence theorems.

Usage:
    python3 parse_theorems.py [--output graph.dot] [--dir LubySequence]

Each node represents a theorem, lemma, or definition, colored by its source file.
Directed edges indicate that one declaration's proof body references another.

Run `dot -Tpdf graph.dot -o graph.pdf` to render the graph.

Requires Python 3.9 or later.
"""

from __future__ import annotations

import re
import sys
import os
import argparse
from pathlib import Path

# Color palette per source file (fill color for nodes)
FILE_COLORS = {
    "Size.lean":            "#AED6F1",  # light blue
    "Basic.lean":           "#A9DFBF",  # light green
    "TrailingZeros.lean":   "#F9E79F",  # light yellow
    "SegmentSequence.lean": "#F5CBA7",  # light orange
    "Equivalence.lean":     "#D7BDE2",  # light purple
}
DEFAULT_COLOR = "#DDDDDD"

# Simpler line-level pattern used in the two-pass approach
DECL_LINE_RE = re.compile(
    r"^(?:public\s+|private\s+|protected\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance)"
    r"\s+([\w'₀-₉ᵤ\u00B2-\u00B9\u2070-\u207F\u2080-\u209F]+)"
)

# Also match lines that are just an attribute followed on the NEXT line by a declaration.
# We handle this by tracking attribute lines.
ATTR_LINE_RE = re.compile(r"^@\[")


def collect_declarations(lean_dir: Path) -> dict[str, str]:
    """
    First pass: collect all declaration names and map name -> filename (basename).
    """
    decl_to_file: dict[str, str] = {}
    for lean_file in sorted(lean_dir.glob("*.lean")):
        fname = lean_file.name
        lines = lean_file.read_text(encoding="utf-8").splitlines()
        for line in lines:
            stripped = line.strip()
            if ATTR_LINE_RE.match(stripped):
                continue
            m = DECL_LINE_RE.match(stripped)
            if m:
                name = m.group(1)
                decl_to_file[name] = fname
    return decl_to_file


def extract_proof_body(lines: list[str], start: int) -> str:
    """
    Extract the proof body for the declaration starting at `start` (0-based line index).
    Returns text from start line to (but not including) the next top-level declaration
    or its preceding doc comment / attribute annotation.
    """
    result: list[str] = [lines[start]]
    # Track pending lines that may belong to the next decl's preamble
    pending: list[str] = []
    i = start + 1
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        # Doc comment opener `/--` always precedes a declaration; treat it as a
        # boundary and stop accumulating body content.
        if stripped.startswith("/--"):
            break
        # Attribute annotation may precede a declaration
        if ATTR_LINE_RE.match(stripped):
            pending.append(line)
            i += 1
            continue
        if DECL_LINE_RE.match(stripped):
            # Don't include pending attribute lines or this declaration line
            break
        # Flush any pending attribute lines that did NOT precede a declaration
        result.extend(pending)
        pending = []
        result.append(line)
        i += 1
    return "\n".join(result)


def find_dependencies(
    body: str,
    all_names: set[str],
    own_name: str,
) -> set[str]:
    """
    Find all references to known declaration names within `body`,
    excluding the declaration itself.
    We use a word-boundary-style match that handles Unicode names.
    """
    deps: set[str] = set()
    for name in all_names:
        if name == own_name:
            continue
        # Escape for regex; use word boundaries where applicable
        escaped = re.escape(name)
        # \b doesn't handle Unicode well; use lookbehind/lookahead for non-word chars.
        # Allow matching after '.' to catch qualified references like Luby.S₂.
        pattern = r"(?<!\w)" + escaped + r"(?![.\w'])"
        if re.search(pattern, body):
            deps.add(name)
    return deps


def build_graph(lean_dir: Path) -> tuple[dict[str, str], dict[str, set[str]]]:
    """
    Build the dependency graph.

    Returns:
        decl_to_file: mapping from declaration name to its source filename
        edges: mapping from declaration name to set of names it depends on
    """
    decl_to_file = collect_declarations(lean_dir)
    all_names = set(decl_to_file.keys())
    edges: dict[str, set[str]] = {name: set() for name in all_names}

    for lean_file in sorted(lean_dir.glob("*.lean")):
        lines = lean_file.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            stripped = line.strip()
            if ATTR_LINE_RE.match(stripped):
                continue
            m = DECL_LINE_RE.match(stripped)
            if m:
                name = m.group(1)
                body = extract_proof_body(lines, i)
                deps = find_dependencies(body, all_names, name)
                edges[name].update(deps)

    return decl_to_file, edges


def sanitize_dot_id(name: str) -> str:
    """
    Convert a Lean declaration name into a valid DOT node identifier.
    DOT identifiers must start with a letter or underscore and contain
    only letters, digits, and underscores. Replace other characters.
    """
    # Replace Unicode subscript digits (₀–₉) and superscript digits (⁰–⁹)
    replacements = {
        "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4",
        "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9",
        "⁰": "0", "¹": "1", "²": "2", "³": "3", "⁴": "4",
        "⁵": "5", "⁶": "6", "⁷": "7", "⁸": "8", "⁹": "9",
        "'": "_prime",
    }
    result = name
    for src, dst in replacements.items():
        result = result.replace(src, dst)
    # Replace remaining non-alphanumeric/underscore characters
    result = re.sub(r"[^\w]", "_", result)
    return result


def write_dot(
    decl_to_file: dict[str, str],
    edges: dict[str, set[str]],
    output_path: Path,
) -> None:
    """Write the dependency graph in Graphviz DOT format."""
    # Only emit edges between known declarations
    all_names = set(decl_to_file.keys())

    with output_path.open("w", encoding="utf-8") as f:
        f.write("digraph LubyDependencies {\n")
        f.write('  rankdir=LR;\n')
        f.write('  node [shape=box, style=filled, fontname="Helvetica", fontsize=9];\n')
        f.write('  edge [arrowsize=0.6];\n')
        f.write("\n")

        # All nodes in a single flat list, colored by source file
        for name in sorted(all_names):
            fname = decl_to_file[name]
            node_id = sanitize_dot_id(name)
            color = FILE_COLORS.get(fname, DEFAULT_COLOR)
            f.write(f'  {node_id} [label="{name}", fillcolor="{color}"];\n')
        f.write("\n")

        # Edges
        for src_name in sorted(all_names):
            src_id = sanitize_dot_id(src_name)
            for dst_name in sorted(edges.get(src_name, set())):
                if dst_name in all_names:
                    dst_id = sanitize_dot_id(dst_name)
                    f.write(f"  {src_id} -> {dst_id};\n")

        f.write("}\n")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate a Graphviz DOT dependency graph for LubySequence theorems."
    )
    parser.add_argument(
        "--dir",
        default="LubySequence",
        help="Directory containing .lean source files (default: LubySequence)",
    )
    parser.add_argument(
        "--output",
        default="graph.dot",
        help="Output DOT file path (default: graph.dot)",
    )
    args = parser.parse_args()

    lean_dir = Path(args.dir)
    if not lean_dir.is_dir():
        print(f"Error: directory not found: {lean_dir}", file=sys.stderr)
        return 1

    output_path = Path(args.output)

    decl_to_file, edges = build_graph(lean_dir)

    total_decls = len(decl_to_file)
    total_edges = sum(len(v) for v in edges.values())
    print(f"Found {total_decls} declarations across {len(set(decl_to_file.values()))} files.")
    print(f"Found {total_edges} dependency edges.")

    write_dot(decl_to_file, edges, output_path)
    print(f"Written: {output_path}")
    print(f"Render with: dot -Tpdf {output_path} -o graph.pdf")
    return 0


if __name__ == "__main__":
    sys.exit(main())
