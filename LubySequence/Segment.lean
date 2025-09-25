import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Utils
import LubySequence.Basic

/-!
Segments are monotonic subsequences of the Luby sequence.
In this file, it's defined a mapping from ℕ to ℕ.
Its index starts from 1.
-/

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
    have s1 : (2 + 2).size = 3 := by simp [size, binaryRec]
    simp [s1] at this
    exact this
  let n' := 2 ^ (n + 2).size - 2
  have n'_def : n' = value_of% n' := by exact rfl
  have n'_is_envelope : n' = 2 ^ n'.size - 2 := by
    simp [n'_def]
    have : (2 ^ (n + 2).size - 2).size = (n + 2).size := by
      refine size_sub ?_ ?_ ?_
      · exact size_pos.mpr (Nat.add_pos_left n_gt_0 2)
      · exact Nat.zero_lt_two 
      · refine Nat.le_self_pow ?_ 2
        · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size3)
    simp [this]
  rw [segment]
  · split
    · expose_names
      have s1 : (2 ^ (n + 2).size - 2 + 2) = 2 ^ (n + 2).size := by
        refine Nat.sub_add_cancel ?_
        · exact Nat.le_self_pow (Nat.ne_zero_of_lt n2size3) 2
      simp [s1]
      replace s1 : (2 ^ (n + 2).size).size = (n + 2).size + 1 := by
        exact size_pow
      simp [s1]
      rw [segment]
      · split
        · expose_names
          have : 2 * 2 ^ ((n + 2).size - 2) = 2 ^ ((n + 2).size - 2 + 1) := by
            exact Eq.symm Nat.pow_succ'
          simp [this]
          grind
        · expose_names
          simp
          have : n = 2 ^ ((n + 2).size - 1) - 2 := by
            rw (occs := .pos [1]) [envelope]
            have : n + 2 = 2 ^ n.size := by
              refine Eq.symm (Nat.eq_add_of_sub_eq ?_ (id (Eq.symm envelope)))
              · exact Nat.le_self_pow (Nat.ne_zero_of_lt nsize2) 2
            simp [this]
            replace : (2 ^ n.size).size - 1 = n.size := by
              have : (2 ^ n.size).size = n.size + 1 := by exact size_pow
              simp [this]
            simp [this]
          exact absurd this h_1
      · intro n_eq_0
        have : ¬n = 0 := by exact Nat.ne_zero_of_lt n_gt_0
        exact absurd n_eq_0 this
    · expose_names
      simp
      simp [←n'_def] at h
      have : n' = 2 ^ ((n' + 2).size - 1) - 2 := by
        simp [n'_def]
        have s1 : (2 ^ (n + 2).size - 2 + 2) = 2 ^ (n + 2).size := by
          refine Nat.sub_add_cancel ?_
          · exact Nat.le_self_pow (Nat.ne_zero_of_lt n2size3) 2
        simp [s1]
        replace s1 : (2 ^ (n + 2).size).size = (n + 2).size + 1 := by
          exact size_pow
        simp [s1]
      exact absurd this h
  · intro x
    have : 2 ^ (n + 2).size ≥ 2 ^ 3 := by
      exact Luby.pow2_le_pow2 3 (n + 2).size n2size3
    replace : 2 ^ (n + 2).size ≥ 8 := by exact this
    replace : ¬2 ^ (n + 2).size - 2 = 0 := by
      exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt this)
    exact absurd x this

/--
Return the length of segment of state `n`.
So `n` starts from zero. -/
def segment_length (n : ℕ) : ℕ := trailing_zeros (segment n) + 1
#eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n, LubySegment.segment_length n))

example : segment_length 0 = 1 := by
  simp [segment_length, segment, trailing_zeros]

theorem segment_length_prop1 : ∀ n > 0, n = 2 ^ n.size - 2 → 
    segment_length (2 ^ (n + 2).size - 2) = 1 + segment_length n := by
  intro n n_gt_0 n_is_envelope
  have n_gt_2 : n ≥ 2 := by
    by_contra n_eq_1
    simp at n_eq_1
    have : n = 1 := by exact Nat.eq_of_le_of_lt_succ n_gt_0 n_eq_1
    simp [this] at n_is_envelope
  have n2size_ge_3 : (n + 2).size ≥ 3 := by
    have s1 : (2 + 2).size ≤ (n + 2).size := by
      have : 2 + 2 ≤ n + 2 := by exact Nat.add_le_add_right n_gt_2 2
      exact size_le_size this
    have : (2 + 2).size = 3 := by simp [size, binaryRec]
    simp [this] at s1
    exact s1
  have pow2nsize : 2 ^ n.size - 2 + 2 = 2 ^ n.size := by
    exact Nat.sub_add_cancel (le_pow (size_pos.mpr n_gt_0))
  have segment_of_n : segment n = 2 ^ (n.size - 1) := by
    rw [segment]
    split
    · expose_names
      rw (occs := .pos [1]) [n_is_envelope]
      simp [pow2nsize]
      replace : (2 ^ n.size).size = n.size + 1 := by exact size_pow
      simp [this]
    · expose_names
      simp
      rw (occs := .pos [2]) [n_is_envelope] at h
      simp [pow2nsize] at h
      have : (2 ^ n.size).size = n.size + 1 := by exact size_pow
      simp [this] at h
      exact absurd n_is_envelope h
    · intro n_eq_0
      have : ¬n = 0 := by exact Nat.ne_zero_of_lt n_gt_0
      exact absurd n_eq_0 this
  rw (occs := .pos [2]) [segment_length]
  simp [segment_of_n]
  have : trailing_zeros (2 ^ (n.size - 1)) = n.size - 1 := by
    exact trailing_zeros_prop3 (n.size - 1)
  simp [this]
  let n' := 2 ^ (n + 2).size - 2
  have n'_def : n' = value_of% n' := by exact rfl
  have n'_is_envelope : n' = 2 ^ n'.size - 2 := by
    simp [n'_def]
    have : (2 ^ (n + 2).size - 2).size = (n + 2).size := by
      refine size_sub ?_ ?_ ?_
      · exact size_pos.mpr (Nat.add_pos_left n_gt_0 2)
      · exact Nat.zero_lt_two 
      · refine Nat.le_self_pow ?_ 2
        · refine Nat.sub_ne_zero_iff_lt.mpr ?_
          · exact lt_of_add_left_lt n2size_ge_3
    simp [this]
  simp [segment_length]
  have : segment (2 ^ (n + 2).size - 2) = 2 ^ ((n + 2).size - 1) := by
    rw [segment]
    simp
    split
    · expose_names
      have : 2 ^ (n + 2).size - 2 + 2 = 2 ^ (n + 2).size := by
        refine Nat.sub_add_cancel ?_
        · refine Nat.le_self_pow ?_ 2
          · exact Nat.ne_zero_of_lt n2size_ge_3
      simp [this]
      replace : (2 ^ (n + 2).size).size = (n + 2).size + 1 := by exact size_pow
      simp [this]
    · expose_names
      have : 2 ^ (n + 2).size - 2 + 2 = 2 ^ (n + 2).size := by
        refine Nat.sub_add_cancel ?_
        · exact le_pow (zero_lt_of_lt n2size_ge_3)
      simp only [this] at h
      replace : (2 ^ (n + 2).size).size - 1 = (n + 2).size := by 
        have : (2 ^ (n + 2).size).size = (n + 2).size + 1 := by exact size_pow
        simp [this]
      simp [this] at h
    · intro x
      have c : 2 ^ (n + 2).size - 2 ≥ 6 := by
        have s1 : 2 ^ (n + 2).size ≥ 2 ^ (2 + 2).size := by
          refine Luby.pow2_le_pow2 (2 + 2).size (n + 2).size ?_
          · exact size_le_size (Nat.add_le_add_right n_gt_2 2)
        have : 2 ^ (2 + 2).size = 8 := by simp [size, binaryRec]
        simp [this] at s1
        exact le_sub_of_add_le s1
      replace c : ¬2 ^ (n + 2).size - 2 = 0 := by exact Nat.ne_zero_of_lt c
      exact absurd x c
  simp [this]
  replace : trailing_zeros (2 ^ ((n + 2).size - 1)) = (n + 2).size - 1 := by
    exact trailing_zeros_prop3 ((n + 2).size - 1)
  simp [this]
  have n_is_envelope' : n + 2 = 2 ^ n.size := by
    refine Eq.symm (Nat.eq_add_of_sub_eq ?_ (id (Eq.symm n_is_envelope)))
    · exact tsub_add_cancel_iff_le.mp pow2nsize
  simp [n_is_envelope']
  replace : (2 ^ n.size).size = n.size + 1 := by exact size_pow
  simp [this]
  replace : n.size - 1 + 1 = n.size := by
    refine Nat.sub_add_cancel ?_
    · have : n.size ≥ 2 := by
        have s1 : n.size ≥ (2 : ℕ).size := by exact size_le_size n_gt_2
        have s2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
        simp [s2] at s1
        exact s1
      exact one_le_of_lt this
  simp [this]
  exact Nat.add_comm n.size 1

theorem segment_length_prop2 : ∀ n > 0, ¬n = 2 ^ n.size - 2 → 
    segment_length (2 ^ (n + 2).size - 2) = segment_length n := by
  sorry

end LubySegment
