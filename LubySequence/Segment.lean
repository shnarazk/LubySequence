import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Utils
import LubySequence.Basic

open Nat

namespace LubySegment

#eval! List.range 8 |>.map (fun n ↦ (n, 2 ^ (n.size - 1), Luby.S₂ n, Luby.luby n))

/--
Return the segment index for `n`.
- `n` starts from 0.
- segment index starts from 1.
-/
def segment (n : ℕ) : ℕ := match n with
  | 0 => 1
  | n =>
    let n' := 2 ^ ((n + 2).size - 2)
    have n'_def : n' = value_of% n' := by exact rfl
    if h : n = 2 * n' - 2
    then n'
    else 
      have order : 2 * n' - 2 < n := by
        sorry
      have decreasing : n - (2 * n' - 2) - 1 < n := by
        have : 2 * n' - 2 ≥ 0 := by exact Nat.zero_le (2 * n' - 2)
        replace : n - (2 * n' - 2) ≤ n := by exact sub_le n (2 * n' - 2)
        by_cases x : n - (2 * n' - 2) ≥ 1
        · exact sub_one_lt_of_le x this
        · simp at x
          refine sub_one_lt_of_le ?_ this
          · exact zero_lt_sub_of_lt order
      n' + segment (n - (2 * n' - 2) - 1)

#eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n))

end LubySegment
