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
-- partial
def segment (n : ℕ) : ℕ := match n with
  | 0 => 1
  | n =>
    let n' := 2 ^ ((n + 2).size - 2)
    have n'_def : n' = value_of% n' := by exact rfl
    if h : n = 2 * n' - 2
    then n'
    else 
      have decreasing : n - (2 * n' - 2) - 1 < n := by
        refine Nat.sub_one_lt_of_le ?_ ?_
        · simp [n'_def]
          by_cases n_eq_0 : n = 0
          · simp [n_eq_0] at *
            simp [size, binaryRec] at n'_def
            have : 0 = 2 * n' - 2 := by simp [n'_def]
            exact absurd this h
          · by_cases n_eq_1 : n = 1
            · simp [n_eq_1] at *
              simp [size, binaryRec]
            · --
              --
              sorry
        · exact Nat.sub_le n (2 * n' - 2)
      n' + segment (n - (2 * n' - 2) - 1)

#eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n))

end LubySegment
