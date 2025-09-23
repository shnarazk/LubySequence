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
    if h : n = 2 ^ ((n + 2).size - 1) - 2
    then 2 ^ ((n + 2).size - 2)
    else
      have n2size : (n + 2).size ≥ 2 := by
        have s1 : (n + 2).size ≥ (0 + 2).size := by
          exact size_le_size (Nat.le_add_left (0 + 2) n)
        have s2 : (0 + 2).size = 2 := by simp [size, binaryRec]
        simp [s2] at s1
        exact s1
      have order : n - (2 ^ ((n + 2).size - 1) - 1) < n := by
        have s1 : 0 < 2 ^ ((n + 2).size - 1) - 1 := by
          refine zero_lt_sub_of_lt ?_
          · exact Nat.one_lt_two_pow (Nat.sub_ne_zero_iff_lt.mpr n2size)
        refine sub_lt ?_ s1
        · by_contra n_eq_0
          simp at n_eq_0
          simp [n_eq_0, size, binaryRec] at h
      2 ^ ((n + 2).size - 2) + segment (n - (2 ^ ((n + 2).size - 1) - 1))

#eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n))
#eval! List.range 8 |>.map (2 ^ ·.succ - 2) |>.map (fun n ↦ (n, LubySegment.segment n))
#eval! List.range 8 
  |>.map (2 ^ ·.succ - 2)
  |>.map (fun n ↦
    ( n,
      2 ^ (n.size + 1) - 2,
      LubySegment.segment n,
      segment (2 ^ (n + 2).size - 2)))

theorem segment_prop1 : ∀ n > 0, n = 2 ^ n.size - 2 → 
    segment (2 ^ (n + 2).size - 2) = 2 * segment n := by
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
  have n2size3 : (n + 2).size ≥ 3 := by
    have : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right n_ge_2 2
    replace : (n + 2).size ≥ (2 + 2).size := by exact size_le_size this
    have s2 : (2 + 2).size = 3 := by simp [size, binaryRec]
    simp [s2] at this
    exact this
  let n' := 2 ^ (n + 2).size - 2
  have n'_def : n' = value_of% n' := by exact rfl
  have n'_is_envelope : n' = 2 ^n'.size - 2 := by
    simp [n'_def]
    have : (2 ^ (n + 2).size - 2).size = (n + 2).size := by
      refine size_sub ?_ ?_ ?_
      · exact size_pos.mpr (Nat.add_pos_left n_gt_0 2)
      · exact Nat.zero_lt_two 
      · refine Nat.le_self_pow ?_ 2
        · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size3)
    simp [this]
  rw [segment]
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
