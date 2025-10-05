import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Utils
import LubySequence.Basic

/-!
Segments are monotonic subsequences in the Luby sequence.
In this file, it's defined as a mapping from ℕ to ℕ.
But its index starts from 1.
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

theorem segment_is_pos : ∀ n : ℕ, segment n > 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [segment.eq_def]
    split
    · exact Nat.one_pos
    · expose_names
      split
      · expose_names
        exact Nat.two_pow_pos ((n + 2).size - 2)
      · expose_names
        simp

theorem segment_is_monotone : ∀ n : ℕ, segment n ≤ segment (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [segment.eq_def]
    split
    · expose_names
      simp
      rw [segment.eq_def]
      split
      · expose_names
        contradiction
      · expose_names
        split
        · expose_names
          simp [size, binaryRec] at h_1
        · expose_names
          simp [size, binaryRec]
    · expose_names
      simp at h
      split
      · expose_names
        rw [segment.eq_def]
        simp
        have n_ge_2 : n ≥ 2 := by
          by_contra n_eq_1
          simp at n_eq_1
          replace n_eq_1 : n = 1 := by
            refine Eq.symm (Nat.le_antisymm ?_ ?_)
            · exact one_le_iff_ne_zero.mpr h
            · exact le_of_lt_succ n_eq_1
          simp [n_eq_1] at *
          simp [size, binaryRec] at h_1
        have n2size_gt_3 : (n + 2).size ≥ 3 := by
          have t1 : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right n_ge_2 2
          replace t1 : (n + 2).size ≥ (2 + 2).size := by exact size_le_size t1
          have t2 : (2 + 2).size = 3 := by simp [size, binaryRec]
          simp [t2] at t1
          exact t1
        have n3size_eq_n2size : (n + 2 + 1).size = (n + 2).size := by
          have h_1' : n + 2 = 2 ^ ((n + 2).size - 1) := by
            have s1 : n + 2 = 2 ^ ((n + 2).size - 1) - 2 + 2 := by
              exact congrFun (congrArg HAdd.hAdd h_1) 2
            have s2 : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
              refine Nat.sub_add_cancel ?_
              · exact le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_gt_3))
            simp [s2] at s1
            exact s1
          rw [h_1']
          refine size_of_pow2 ?_ ?_
          · exact le_sub_one_of_lt n2size_gt_3
          · refine Nat.one_lt_two_pow_iff.mpr ?_
            · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_gt_3)
        split <;> simp [n3size_eq_n2size]
      · expose_names
        simp
        rw (occs := .pos [2]) [segment.eq_def]
        split
        · expose_names
          contradiction
        · split
          · expose_names
            have n2_is_envelope : n + 2 = 2 ^ ((n + 1 + 2).size - 1) - 1 := by
              replace h_3 : n = 2 ^ ((n + 1 + 2).size - 1) - 2 - 1 := by
                exact Nat.eq_sub_of_add_eq h_3
              have : 2 ^ ((n + 1 + 2).size - 1) - 2 - 1 = 2 ^ ((n + 1 + 2).size - 1) - 1 - 2 := by
                exact rfl
              simp [this] at h_3
              replace h_3 : n + 2 = 2 ^ ((n + 1 + 2).size - 1) - 1 - 2 + 2 := by
                exact congrFun (congrArg HAdd.hAdd h_3) 2
              have : 2 ^ ((n + 1 + 2).size - 1) - 1 - 2 + 2 = 2 ^ ((n + 1 + 2).size - 1) - 1 := by
                refine Nat.sub_add_cancel ?_
                · have : (n + 1 + 2).size ≥ 3 := by
                    replace h : n ≥ 1 := by exact one_le_iff_ne_zero.mpr h
                    have : n + 1 + 2 ≥ 1 + 1 + 2 := by
                      exact Nat.add_le_add_right (Nat.add_le_add_right h 1) 2
                    replace : (n + 1 + 2).size ≥ (1 + 1 + 2).size := by exact size_le_size this
                    have s : (1 + 1 + 2).size = 3 := by simp [size, binaryRec]
                    simp [s] at this
                    exact this
                  replace : 2 ^ ((n + 1 + 2).size - 1) ≥ 4 := by
                    have s1 : 2 ^ ((n + 1 + 2).size - 1) ≥ 2 ^ (3 - 1) := by
                      refine Nat.pow_le_pow_right Nat.zero_lt_two ?_
                      · exact Nat.sub_le_sub_right this 1
                    have s2 : 2 ^ (3 - 1) = 4 := by exact rfl
                    simp [s2] at s1
                    exact s1
                  grind
              simp only [this] at h_3
              exact h_3
            have n3size_eq_n2size : (n + 2 + 1).size = (n + 2).size + 1 := by
              let x := n + 2 + 1
              have x_def : x = value_of% x := by exact rfl
              simp [←x_def]
              have : x - 1 = n + 2 := by exact rfl
              simp [←this]
              replace n2_is_envelope : n + 2 + 1 = 2 ^ ((n + 2 + 1).size - 1) := by
                exact Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mp) (id (Eq.symm n2_is_envelope)))
              simp [←x_def] at n2_is_envelope
              refine size_of_pow2_eq_size_of_envelope_add_1' ?_ ?_
              · simp [x_def]
              · exact n2_is_envelope
            have : n - (2 ^ ((n + 2).size - 1) - 1) = 2 ^ ((n + 2).size - 1) - 2 := by
              replace h_3 : n = 2 ^ ((n + 1 + 2).size - 1) - 2 - 1 := by
                exact Nat.eq_sub_of_add_eq h_3
              rw (occs := .pos [1]) [h_3]
              simp [n3size_eq_n2size]
              replace : 2 ^ (n + 2).size = 2 ^ ((n + 2).size - 1) + 2 ^ ((n + 2).size - 1) := by
                refine Eq.symm (Nat.two_pow_pred_add_two_pow_pred ?_)
                · exact size_pos.mpr (zero_lt_succ (n + 1))
              simp [this]
              rw [Nat.sub_sub]
              have : 1 + (2 ^ ((n + 2).size - 1) - 1) = 2 ^ ((n + 2).size - 1) := by
                rw [add_comm]
                exact Nat.sub_add_cancel (Nat.one_le_two_pow)
              simp [this]
              rw [Nat.sub_sub]
              exact Nat.add_sub_add_right (2 ^ ((n + 2).size - 1)) (2 ^ ((n + 2).size - 1)) 2
            simp [this]
            have : segment (2 ^ ((n + 2).size - 1) - 2) ≤ 2 ^ ((n + 2).size - 1) - 2 + 1 := by
              sorry
            sorry
            --

            -- これ以上splitしないはずでは
            /-
            rw [segment.eq_def]
            split
            · expose_names
              have : n = 1 := by
                by_cases n_le_1 : n ≤ 1
                · have : n = 1 := by
                    refine Eq.symm (Nat.le_antisymm ?_ n_le_1)
                    · exact one_le_iff_ne_zero.mpr h
                  exact this
                · simp at n_le_1
                  replace n_le_1 : 2 ≤ n := by exact n_le_1
                  have s1 : (2 + 2).size ≤ (n + 2).size := by
                    exact size_le_size (Nat.add_le_add_right n_le_1 2)
                  have s2 : (2 + 2).size = 3 := by simp [size, binaryRec]
                  simp [s2] at s1
                  have : 2 ^ ((n + 2).size - 1) - 2 > 0 := by
                    have t1 : (n + 2).size - 1 ≥ 2 := by exact le_sub_one_of_lt s1
                    have t2 : 2 ^ ((n + 2).size - 1) ≥ 2 ^ 2 := by
                      exact Luby.pow2_le_pow2 2 ((n + 2).size - 1) t1
                    replace t2 : 2 ^ ((n + 2).size - 1) - 2 ≥ 2 ^ 2 - 2 := by
                      exact Nat.sub_le_sub_right t2 2
                    simp at t2
                    exact zero_lt_of_lt t2
                  replace : ¬2 ^ ((n + 2).size - 1) - 2 = 0 := by exact Nat.ne_zero_of_lt this
                  exact absurd heq this
              simp [this, size, binaryRec]
            · expose_names
              have n_ge_1 : n ≥ 1 := by exact one_le_iff_ne_zero.mpr h
              have n2size_ge_2 : (n + 2).size ≥ 2 := by
                have s1 : n + 2 ≥ 1 + 2 := by exact Nat.add_le_add_right n_ge_1 2
                replace s1 : (n + 2).size ≥ (1 + 2).size := by exact size_le_size s1
                have s2 : (1 + 2).size = 2 := by simp [size, binaryRec] 
                simp [s2] at s1
                exact s1
              split
              · expose_names
                simp [n3size_eq_n2size]
                have : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
                  exact Nat.sub_add_cancel (le_pow (zero_lt_sub_of_lt n2size_ge_2))
                simp [this]
                replace : (2 ^ ((n + 2).size - 1)).size = (n + 2).size := by 
                  have : (2 ^ ((n + 2).size - 1)).size = (n + 2).size - 1 + 1 := by 
                    exact size_pow
                  simp [this]
                  replace : (n + 2).size - 1 + 1 = (n + 2).size := by
                    exact Nat.sub_add_cancel (one_le_of_lt n2size_ge_2)
                  simp [this]
                simp [this]
                replace :
                    2 ^ ((n + 2).size - 2) + 2 ^ ((n + 2).size - 2) = 2 ^ ((n + 2).size - 1) := by
                  rw [←Nat.two_mul]
                  have : 2 * 2 ^ ((n + 2).size - 2) = 2 ^ ((n + 2).size - 2 + 1) := by
                    exact Eq.symm Nat.pow_succ'
                  simp [this]
                  grind
                simp [this]
              · expose_names
                simp
                have aux : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by grind
                simp [aux]
                replace aux : (2 ^ ((n + 2).size - 1)).size = (n + 2).size := by
                  have : (2 ^ ((n + 2).size - 1)).size = (n + 2).size - 1 + 1 := by
                    exact size_pow
                  simp [this]
                  grind
                simp [aux]
                rw [←add_assoc]
                --
                sorry
            -/
          · expose_names
            simp
            -- これも帰納法に持ち込む
            sorry

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

theorem segment_prop2 : ∀ n > 0, ¬n = 2 ^ n.size - 2 →
    segment n = 2 ^ ((n + 2).size - 2) + segment (n - (2 ^ ((n + 2).size - 1) - 1)) := by
  intro n n_gt_0 n_ne_envelope
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
      simp [n_eq_0, size] at n_ne_envelope
  rw [segment]
  · split
    · expose_names
      have n_ge_2 : n ≥ 2 := by
        by_contra n_eq_1
        simp at n_eq_1
        replace n_eq_1 : n = 1 := by exact Nat.eq_of_le_of_lt_succ n_gt_0 n_eq_1
        simp [n_eq_1] at *
        simp [size, binaryRec] at h
      have n2size_ge_2 : (n + 2).size ≥ 3 := by
        have s1 : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right n_ge_2 2
        have s2 : (2 + 2).size = 3 := by simp [size, binaryRec]
        rw [←s2]
        exact size_le_size s1
      have : n = 2 ^ n.size - 2 := by
        rw (occs := .pos [2]) [h]
        have s1 : (2 ^ ((n + 2).size - 1) - 2).size = (n + 2).size - 1 := by
          refine size_sub ?_ ?_ ?_
          · exact zero_lt_sub_of_lt n2size
          · exact Nat.zero_lt_two
          · refine Nat.le_self_pow ?_ 2
            · exact Nat.sub_ne_zero_iff_lt.mpr (lt_sub_of_add_lt n2size_ge_2)
        simp [s1]
        exact h
      exact absurd this n_ne_envelope
    · expose_names
      simp
  · intro n_eq_0
    simp [n_eq_0] at *

theorem segment_limit {n : ℕ} (h : n > 0) : segment n ≤ n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [segment.eq_def]
    split
    · expose_names ; contradiction
    · expose_names
      split
      have n_ge_2 : n ≥ 2 := by
        by_cases n_eq_1 : n = 1
        · expose_names
          simp [n_eq_1] at *
          simp [size, binaryRec] at h_2
        · expose_names
          replace h : n ≥ 1 := by exact h
          by_cases n_ge_2 : n ≥ 2
          · exact n_ge_2
          · replace n_ge_2 : n < 2 := by exact Nat.lt_of_not_le n_ge_2
            replace n_ge_2 : n ≤ 1 := by exact le_of_lt_succ n_ge_2
            have : n = 1 := by exact Eq.symm (Nat.le_antisymm h n_ge_2)
            exact absurd this n_eq_1
      have n2size_ge_3 : (n + 2).size ≥ 3 := by
        have s1 : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right n_ge_2 2
        replace s1 : (n + 2).size ≥ (2 + 2).size := by exact size_le_size s1
        have s2 : (2 + 2).size = 3 := by simp [size, binaryRec]
        simp [s2] at s1
        exact s1
      · expose_names
        replace h_2 : n + 1 = 2 ^ ((n + 2).size - 1) - 1 := by
          have : n + 1 = 2 ^ ((n + 2).size - 1) - 2 + 1 := by
            exact congrFun (congrArg HAdd.hAdd h_2) 1
          rw [this]
          grind
        simp [h_2]
        have : 2 ^ ((n + 2).size - 1) = 2 ^ ((n + 2).size - 2) + 2 ^ ((n + 2).size - 2) := by
          have : 2 ^ ((n + 2).size - 1) = 2 * 2 ^ ((n + 2).size - 1 - 1) := by
            refine Eq.symm (mul_pow_sub_one ?_ 2)
            · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)
          simp [this]
          replace : (n + 2).size - 1 - 1 = (n + 2).size - 2 := by exact rfl
          simp [this]
          exact Nat.two_mul (2 ^ ((n + 2).size - 2))
        simp only [this]
        rw [Nat.add_sub_assoc]
        · exact Nat.le_add_right (2 ^ ((n + 2).size - 2)) (2 ^ ((n + 2).size - 2) - 1)
        · exact Nat.one_le_two_pow
      · expose_names
        simp
        have ih1 : n - (2 ^ ((n + 2).size - 1) - 1) < n := by sorry
        have ih2 : n - (2 ^ ((n + 2).size - 1) - 1) > 0 := by sorry
        have ih' :
            segment (n - (2 ^ ((n + 2).size - 1) - 1)) ≤ n - (2 ^ ((n + 2).size - 1) - 1) + 1 := by
          exact ih (n - (2 ^ ((n + 2).size - 1) - 1)) ih1 ih2
        replace ih' :
            2 ^ ((n + 2).size - 2) + segment (n - (2 ^ ((n + 2).size - 1) - 1))
            ≤ 2 ^ ((n + 2).size - 2) + (n - (2 ^ ((n + 2).size - 1) - 1) + 1) := by
          exact Nat.add_le_add_iff_left.mpr (ih (n - (2 ^ ((n + 2).size - 1) - 1)) ih1 ih2)
        have :
            2 ^ ((n + 2).size - 2) + (n - (2 ^ ((n + 2).size - 1) - 1) + 1)
            ≤ n + 1 := by
          sorry
        exact Nat.le_trans ih' this


 /-

      
        rw (occs := .pos [1]) [h_2]
        have : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
          refine Nat.sub_add_cancel ?_
          · refine le_pow ?_
            · sorry
        simp [this]

      rw [h_2]
      have : (2 ^ ((n + 2).size - 2)).size = (n + 2).size - 2 + 1 := by exact size_pow
      simp [this]
      sorry
    · expose_names
      simp
      sorry
-/

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
      · exact Nat.le_self_pow (Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)) 2
    simp [this]
  simp [segment_length]
  have : segment (2 ^ (n + 2).size - 2) = 2 ^ ((n + 2).size - 1) := by
    rw [segment]
    simp
    split
    · expose_names
      have : 2 ^ (n + 2).size - 2 + 2 = 2 ^ (n + 2).size := by
        exact Nat.sub_add_cancel (Nat.le_self_pow (Nat.ne_zero_of_lt n2size_ge_3) 2)
      simp [this]
      replace : (2 ^ (n + 2).size).size = (n + 2).size + 1 := by exact size_pow
      simp [this]
    · expose_names
      have : 2 ^ (n + 2).size - 2 + 2 = 2 ^ (n + 2).size := by
        exact Nat.sub_add_cancel (le_pow (zero_lt_of_lt n2size_ge_3))
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

#eval List.range 32
  -- |>.map (fun n ↦ (n, segment n, 2 ^ ((n + 1).size - 1)))
  |>.filter (fun n ↦ ¬segment n = 2 ^ ((n + 1).size - 1))
  |>.map (fun n ↦ (n, segment_length (n - (2 ^ ((n + 2).size - 1) - 1)), segment_length n))

theorem segment_length_prop2 : ∀ n > 0, ¬n = 2 ^ n.size - 2 →
    segment_length (n - (2 ^ ((n + 2).size - 1) - 1)) = segment_length n := by
  intro n n_gt_0 n_ne_envelope
  simp [segment_length]
  rw [segment_prop2 n n_gt_0 n_ne_envelope]
  let x := 2 ^ ((n + 2).size - 1)
  have x_def : x = value_of% x := by exact rfl
  simp [←x_def]
  rw [add_comm]
  refine Eq.symm (trailing_zeros_prop1' (segment (n - (x - 1))) ?_ ((n + 2).size - 2) ?_)
  · exact segment_is_pos (n - (x - 1))
  · simp [x]
    have t1 : n - (2 ^ ((n + 2).size - 1) - 1) < 2 ^ ((n + 2).size - 1) - 1 := by
      sorry
    have t2 :
        segment (n - (2 ^ ((n + 2).size - 1) - 1)) < segment (2 ^ ((n + 2).size - 1) - 1) := by
      sorry
    -- FIXME
    --
    sorry

end LubySegment
