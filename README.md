# O(1) implementation of LubySequence

<img width="539" alt="Image" src="https://github.com/user-attachments/assets/3a6b91de-ca05-4cf4-8939-378b366f0cf5" />

A Lean 4 library focused on proving the correctness of a new O(1) implementation of the Luby sequence based on segments, along with supporting lemmas on natural numbers and binary representations, and notes/papers about the construction.

The Luby sequence was introduced in: Michael Luby, Alistair Sinclair, and David Zuckerman. “Optimal Speedup of Las Vegas Algorithms.” _Information Processing Letters_, 47(4): 173–180, 1993.
It is sometimes used as a restart schedule in randomized algorithms (notably SAT solvers). This repository provides a Lean 4 library you can build locally.

## Overview

- Formal definitions of zero-based and one-based variants of the Luby sequence
- A segment-based O(1) implementation (`SegmentSequence`, `SegmentedState`) with correctness proofs
- Supporting lemmas on binary sizes and trailing zeros
- Proofs connecting the segment-based implementation to the recursive definition
- Accompanying notes in Typst describing the definitions and complexity intuition

If you just want to browse the code, start with the top-level module:
- `LubySequence.lean` (imports the core modules)

## Modules

- `LubySequence.Size`
  - Supporting lemmas about the binary size (`Nat.size`) of natural numbers.

- `LubySequence.TrailingZeros`
  - Defines `trailing_zeros` and proves its key properties.

- `LubySequence.Basic`
  - Defines the Luby sequence and supporting functions.
  - Includes lemmas relating natural numbers to their binary representation (e.g., using `Nat.size`).
  - Introduces “envelope” utilities used by other modules.

- `LubySequence.SegmentSequence`
  - Defines `Segment` and the O(1) segment-based computation of Luby values.
  - Proves segment boundary properties and monotonicity.

- `LubySequence.SegmentedState`
  - Defines `SegmentedState`, a stateful O(1) iterator over the Luby sequence.
  - Proves correctness of the iterator with respect to the recursive definition.

- `LubySequence.Equivalence`
  - Proves that the segment-based implementation agrees with the recursive definition.
  - Contains completed proofs connecting segment indices to envelope depths.

- `LubySequence` (root)
  - Umbrella module that imports `Basic`, `SegmentSequence`, `SegmentedState`, and `Equivalence`.

## Building

This is a Lean 4 project managed with Lake and using mathlib.

### Requirements

- Lean toolchain managed by elan (recommended)
- Lake (comes with Lean toolchain)
- Internet access on first build to fetch mathlib

The project pins the Lean version via `lean-toolchain` and depends on:
- mathlib `v4.28.0-rc1` (as configured in `lakefile.toml`)

### Build with Lake

- Install Lean via elan: https://leanprover-community.github.io/get_started.html
- Clone this repository
- From the project root, run:

```
lake update
lake build
```

This will fetch dependencies (mathlib) and compile the library.

### Build inside Nix dev shell (optional)

This repo includes a `flake.nix` that provides a development shell with:
- elan + Lean + Lake
- typst + tinymist (for Typst docs)

To enter the dev shell:

- With flakes:
  ```
  nix develop
  ```
- If you use direnv (there’s a `.envrc` in the repo), allow it in the project directory to auto-enter the shell.

Once in the shell, build as usual:

```
lake update
lake build
```

## Documentation and Notes

- Typst documents in repo root:
  - `memo.typ` and `presen.typ`, with prebuilt PDFs (`memo.pdf`, `presen.pdf`) included.
  - Build with:
    ```
    typst compile memo.typ
    typst compile presen.typ
    ```
  - The Nix dev shell includes `typst` and the `tinymist` LSP for editor support.

- A `graph.dot` is included for visualizations. If you have Graphviz installed:
  ```
  dot -Tpdf graph.dot -o graph.pdf
  ```
  To regenerate the graph from the current source files, run:
  ```
  python3 parse_theorems.py
  ```
  Each node in the graph represents a theorem, lemma, or definition and is colored
  by its source file. Directed edges indicate proof dependencies.

## Acknowledgments

- Built on Lean 4 and mathlib.
