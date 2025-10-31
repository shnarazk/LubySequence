import Mathlib.Data.Nat.Size

/-!
# Size Notation Macros

This module provides convenient macro notations for computing the size (bit length)
of expressions involving `n + 1` and `n + 2`.

## Notations

- `n.size₁` expands to `(n + 1).size`
- `n.size₂` expands to `(n + 2).size`

These macros are useful when working with the Luby sequence and related computations
where we frequently need to compute the size of shifted natural numbers.
-/

/--
Macro notation for `(n + 1).size`.
Usage: `n.size₁` expands to `(n + 1).size`
-/
macro:max t:term ".size₁" : term => `(($t + 1).size)

/--
Macro notation for `(n + 2).size`.
Usage: `n.size₂` expands to `(n + 2).size`
-/
macro:max t:term ".size₂" : term => `(($t + 2).size)
