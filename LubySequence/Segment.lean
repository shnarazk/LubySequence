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
        simp [n'_def]
        by_cases n_le_1 : n ≤ 1
        · have cases : n = 0 ∨ n = 1 := by exact le_one_iff_eq_zero_or_eq_one.mp n_le_1
          rcases cases with n_eq_0|n_eq_1
          · simp [n_eq_0, size, binaryRec] at *
            simp [n'_def] at h
          · simp [n_eq_1, size, binaryRec] at *
        · have n_ge_2 : n ≥ 2 := by
            have : n > 1 := by exact Nat.lt_of_not_le n_le_1
            exact this
          have nsize2 : (n + 2).size ≥ 2 := by
            have t1 : (n + 2).size ≥ (2 + 2).size := by
              refine size_le_size ?_
              · exact Nat.add_le_add_right n_ge_2 2
            have t2 : (2 + 2).size = 3 := by simp [size, binaryRec]
            simp [t2] at t1
            exact le_of_add_left_le t1
          have : 2 * 2 ^ ((n + 2).size - 2) = 2 ^ ((n + 2).size - 1) := by
            have : 2 * 2 ^ ((n + 2).size - 2) = 2 ^ ((n + 2).size - 2 + 1) := by
              exact Eq.symm Nat.pow_succ'
            simp [this]
            rw [add_comm]
            refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add' h).mp) ?_ rfl)
            · exact le_sub_one_of_lt nsize2
          simp [this]
          refine Nat.sub_lt_right_of_lt_add ?_ ?_
          · exact le_pow (zero_lt_sub_of_lt nsize2)
          · have t1 : 2 ^ ((n + 2).size - 1) ≤ n + 2 := by
              exact n_ge_subenvelope (Nat.le_add_left 1 (n + 1))
            have t2 : ¬2 ^ ((n + 2).size - 1) = n + 2 := by
              by_contra envelope
              have : n = 2 * n' - 2 := by simp [n'_def, this, envelope]
              exact absurd this h
            exact Nat.lt_of_le_of_ne t1 t2
      have decreasing : n - (2 * n' - 2) - 1 < n := by
        have : 2 * n' - 2 ≥ 0 := by exact Nat.zero_le (2 * n' - 2)
        replace : n - (2 * n' - 2) ≤ n := by exact sub_le n (2 * n' - 2)
        by_cases x : n - (2 * n' - 2) ≥ 1
        · exact sub_one_lt_of_le x this
        · exact sub_one_lt_of_le (zero_lt_sub_of_lt order) this
      n' + segment (n - (2 * n' - 2) - 1)

#eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n))

end LubySegment
