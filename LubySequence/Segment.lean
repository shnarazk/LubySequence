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
partial
def segment (n : ℕ) : ℕ := match n with
  | 0 => 1
  | n =>
    let n' := 2 ^ (n.size - 1)
    have n'_def : n' = value_of% n' := by exact rfl
    if h : n = 2 * n' - 2
    then n'
    else
      /-
      have order : 2 * n' - 2 < n := by
        simp [n'_def]
        by_cases n_le_1 : n ≤ 1
        · have cases : n = 0 ∨ n = 1 := by exact le_one_iff_eq_zero_or_eq_one.mp n_le_1
          rcases cases with n_eq_0|n_eq_1
          · simp [n_eq_0, size] at *
            simp [n'_def] at h
          · simp [n_eq_1, size] at *
        · have n_ge_2 : n ≥ 2 := by
            have : n > 1 := by exact Nat.lt_of_not_le n_le_1
            exact this
          have nsize2 : n.size ≥ 2 := by
            have t1 : n.size ≥ (2 : ℕ).size := by
              exact size_le_size n_ge_2
            have t2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
            simp [t2] at t1
            exact t1
          have : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 1) := by
            have : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 2 + 1) := by
              exact Eq.symm Nat.pow_succ'
            simp [this]
            rw [add_comm]
            refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add' h).mp) ?_ rfl)
            · exact le_sub_one_of_lt nsize2
          simp [this]
          refine Nat.sub_lt_right_of_lt_add ?_ ?_
          · exact le_pow (zero_lt_sub_of_lt nsize2)
          · have t1 : 2 ^ (n.size - 1) ≤ n := by
              exact n_ge_subenvelope (one_le_of_lt n_ge_2)
            have t2 : 2 ^ (n.size - 1) < n + 1 := by exact Order.lt_add_one_iff.mpr t1
            exact lt_succ_of_lt t2
      have decreasing : n - (2 * n' - 2) - 1 < n := by
        have : 2 * n' - 2 ≥ 0 := by exact Nat.zero_le (2 * n' - 2)
        replace : n - (2 * n' - 2) ≤ n := by exact sub_le n (2 * n' - 2)
        by_cases x : n - (2 * n' - 2) ≥ 1
        · exact sub_one_lt_of_le x this
        · exact sub_one_lt_of_le (zero_lt_sub_of_lt order) this
      -/
      2 ^ ((n + 2).size - 2) + 
      segment (n - (2 ^ ((n + 2).size - 1) - 1))

#eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n))
#eval! List.range 8 |>.map (2 ^ ·.succ - 2) |>.map (fun n ↦ (n, LubySegment.segment n))
#eval! List.range 8 
  |>.map (2 ^ ·.succ - 2)
  |>.map (fun n ↦
    ( n,
      2 ^ (n.size + 1) - 2,
      LubySegment.segment n,
      segment (2 ^ (n.size + 1) - 2)))

theorem segment_prop1 : ∀ n > 0, n = 2 ^ n.size - 2 → 
    segment (2 ^ (n.size + 1) - 2) = 2 * segment n := by
  intro n n_gt_0 envelope
  have n_ge_2 : n ≥ 2 := by
    by_contra n_eq_1
    simp at n_eq_1
    replace n_eq_1 : n = 1 := by exact Nat.eq_of_le_of_lt_succ n_gt_0 n_eq_1
    simp [n_eq_1] at envelope
  have nsize2 : n.size ≥ 2 := by
    have t1 : n.size ≥ (2 : ℕ).size := by exact size_le_size n_ge_2
    have t2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
    simp [t2] at t1
    exact t1
  -- have n1 : n = 2 * 2 ^ (n.size - 2) - 2 := by sorry
  sorry
/-
  rewrite (occs := .pos [1]) [segment]
  · rewrite (occs := .pos [2]) [segment]
    · expose_names
      simp
      split
      · expose_names
        have : (2 ^ (n.size + 1) - 2).size = n.size + 1 := by
          refine size_sub ?_ ?_ ?_
          · exact zero_lt_succ n.size
          · exact Nat.zero_lt_two
          · simp
            refine le_pow ?_
            exact size_pos.mpr n_gt_0
        simp [this]
        replace : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 1) := by
          replace t1 : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 2 + 1) := by
            exact Eq.symm Nat.pow_succ'
          replace t2 : n.size - 2 + 1 = n.size - 1 := by grind
          simp [t2] at t1
          exact t1
        simp [this]
        sorry
      · expose_names
        --
        sorry
    · expose_names
      intro x
      simp [x] at *
  · intro x
    -- have t1 : n ≥ 1 := by exact n_gt_0
    have t1 : n.size ≥ (1 : ℕ).size := by exact size_le_size n_gt_0
    have : (1 : ℕ).size = 1 := by exact size_one
    simp [this] at t1
    replace : n.size + 1 ≥ 2 := by exact le_add_of_sub_le t1
    replace : 2 ^ (n.size + 1) ≥ 2 ^ 2 := by exact Luby.pow2_le_pow2 2 (n.size + 1) this
    simp at this
    have c : 4 - 2 ≤ 2 ^ (n.size + 1) - 2 := by
      exact Nat.sub_le_sub_right this 2
    simp [x] at c
-/

end LubySegment
