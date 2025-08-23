# Theorem Dependency Graph

This directory contains the mutual dependency graph of theorems defined in the LubySequence/*.lean files.

## Files Generated

- `graph.dot` - GraphViz DOT format file containing the theorem dependency graph
- `parse_theorems.py` - Python script used to parse Lean files and generate the graph

## Graph Contents

The dependency graph contains **40 theorems** across 4 Lean files with **31 dependency edges** between them:

### Files and Theorem Counts
- `Basic.lean` - 11 theorems (envelope properties, Luby sequence properties)
- `State.lean` - 10 theorems (LubyState properties and proofs)
- `Tree.lean` - 17 theorems (LubyTree properties and utilities)
- `Equivalence.lean` - 2 theorems (equivalence proofs between different representations)

### Most Referenced Theorems
1. `envelope_prop1` - 5 references
2. `envelope_prop2` - 5 references  
3. `size_is_two_sub_sizes_add_one` - 5 references
4. `pow2_le_pow2` - 3 references
5. `luby_value_at_segment_beg` - 3 references

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

Each file is represented as a different colored cluster:
- Basic.lean: Light cyan
- State.lean: Light pink  
- Tree.lean: Light green
- Equivalence.lean: Light yellow

Dependencies show which theorems reference/use other theorems in their proofs.