# LubySequence

<img width="539" height="221" alt="Image" src="https://github.com/user-attachments/assets/db6c12f4-22f2-4416-847a-4321ad35566c" />

A Lean 4 formalization and study of the Luby sequence, including multiple equivalent characterizations (recursive, tree-based, and iterator/state-based), supporting lemmas on natural numbers and binary representations, and notes/papers about the construction.

The Luby sequence was introduced in: Michael Luby, Alistair Sinclair, and David Zuckerman. “Optimal Speedup of Las Vegas Algorithms.” _Information Processing Letters_, 47(4): 173–180, 1993.
It is sometimes used as a restart schedule in randomized algorithms (notably SAT solvers). This repository explores the sequence’s structure and equivalences and provides a Lean library you can build locally.

## Overview

- Formal definitions of zero-based and one-based variants of the Luby sequence
- A tree model that captures the “envelope” structure of Luby segments
- An iterator/state-machine view that produces the sequence step-by-step
- Proofs connecting the models and basic facts about binary sizes
- Accompanying notes in Typst describing the definitions and complexity intuition

If you just want to browse the code, start with the top-level module:
- `LubySequence/LubySequence.lean` (imports the core modules)

## Modules

- `LubySequence.Basic`
  - Defines the Luby sequence and supporting functions.
  - Includes lemmas relating natural numbers to their binary representation (e.g., using `Nat.size`).
  - Introduces “envelope” utilities used by other modules.

- `LubySequence.Tree`
  - A tree-based model (`LubyTree`) with levels (starting at 1) and element indices (starting at 0).
  - Defines envelope size/depth and captures the notion of the smallest tree containing a given number of elements.

- `LubySequence.State`
  - A state-machine/iterator model (`LubyState`) that steps through the sequence.
  - Tracks segment and local indices and shows how successive states produce the Luby values.

- `LubySequence.Equivalence`
  - Bridges the models: shows how the iterator/state and tree envelopes agree with the recursive definition.
  - Contains in-progress and completed proofs connecting segment indices to envelope depths.

- `Utils`
  - Small general lemmas and utilities for natural numbers, modular arithmetic, and binary size that the main development relies on.

- `LubySequence` (root)
  - Umbrella module that imports `Basic`, `Tree`, `State`, and `Equivalence`.

## Building

This is a Lean 4 project managed with Lake and using mathlib.

### Requirements

- Lean toolchain managed by elan (recommended)
- Lake (comes with Lean toolchain)
- Internet access on first build to fetch mathlib

The project pins the Lean version via `lean-toolchain` and depends on:
- mathlib `v4.23.0` (as configured in `lakefile.toml`)

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
- If you use direnv (there’s a `.direnv/` in the repo), allow it in the project directory to auto-enter the shell.

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

## Acknowledgments

- Built on Lean 4 and mathlib.
