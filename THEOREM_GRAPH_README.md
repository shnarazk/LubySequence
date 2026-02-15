# Theorem Dependency Graph

This directory contains the mutual dependency graph of theorems defined in the LubySequence/*.lean files.

## Files Generated

- `graph.dot` - GraphViz DOT format file containing the theorem dependency graph
- `parse_theorems.py` - Python script used to parse Lean files and generate the graph

## Graph Contents

The dependency graph contains **123 theorems** across 6 Lean files with **129 dependency edges** between them:

### Files and Theorem Counts
- `Basic.lean` - Core definitions and basic properties
- `Equivalence.lean` - Equivalence proofs between different representations
- `SegmentSequence.lean` - Segment sequence theorems
- `Size.lean` - Size-related properties and lemmas
- `TrailingZeros.lean` - Trailing zeros theorems
- `Utils.lean` - Utility theorems

### Most Referenced Theorems
1. `size_add` - 8 references
2. `size_of_pow2_eq_self_add_one` - 8 references
3. `n_ge_subenvelope` - 6 references
4. `size_sub` - 6 references
5. `envelope_prop1` - 5 references

## Visualization

To visualize the graph, you can use GraphViz tools:

```bash
# Generate PNG image
dot -Tpng graph.dot -o theorem_dependencies.png

# Generate SVG (scalable)
dot -Tsvg graph.dot -o theorem_dependencies.svg

# Generate PDF
dot -Tpdf graph.dot -o theorem_dependencies.pdf
```

## Graph Structure

The graph uses a hierarchical layout with:
- **Top-to-bottom direction** (rankdir=TB)
- **Clustered subgraphs** for each Lean file with different colors
- **Blue arrows** showing dependency relationships (A → B means A depends on B)
- **Rectangular nodes** representing individual theorems

Each file is represented as a different colored cluster with consistent color coding for easy identification

Dependencies show which theorems reference/use other theorems in their proofs.