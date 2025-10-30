import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Utils
import LubySequence.Basic
import LubySequence.Segment

namespace LubySegment

open Nat

-- #eval List.range 64 |>.all (fun n ↦ (segment  n ≤ 2 ^ ((n + 1).size - 1)))
/--
For n ≥ 2, the segment index is bounded by 2^((n+1).size - 1).
This provides a logarithmic upper bound on segment indices.
-/
theorem segment_limit2 {n : ℕ} (n_ge : n ≥ 2) : segment n ≤ 2 ^ ((n + 1).size - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    replace n_ge : n = 2 ∨ n > 2 := by exact LE.le.eq_or_lt' n_ge
    rcases n_ge with n_eq_2|n_ge
    · simp [n_eq_2, segment]
    · replace n_ge : n = 3 ∨ n > 3 := by exact LE.le.eq_or_lt' n_ge
      rcases n_ge with n_eq_3|n_ge_4
      · simp [n_eq_3, segment, size, binaryRec]
      · replace n_ge_4 : n ≥ 4 := by exact n_ge_4
        have nsize_ge_3 : n.size ≥ 3 := by exact size4_add_0_ge_2 n_ge_4
        have n1size_ge_3 : (n + 1).size ≥ 3 := by
          exact size4_add_0_ge_2 (le_add_right_of_le n_ge_4)
        have n2size_ge_3 : (n + 2).size ≥ 3 := by
          exact size2_add_2_ge_2 (le_of_add_left_le n_ge_4)
        have pow2_nsize_minus_1_divide :
            2 ^ (n.size - 1) = 2 ^ (n.size - 2) + 2 ^ (n.size - 2) := by
          have s1 : 2 ^ (n.size - 1) = 2 ^ (n.size - 1 - 1) * 2 := by
            exact
              Eq.symm (two_pow_pred_mul_two (zero_lt_sub_of_lt (lt_of_add_left_lt nsize_ge_3)))
          have s2 : n.size - 1 - 1 = n.size - 2 := by exact rfl
          simp [s2] at s1
          rw [mul_two] at s1
          exact s1
        by_cases n_is_pow2 : n = 2 ^ (n.size - 1)
        · have n1_ne_pow2 : ¬n + 1 = 2 ^ ((n + 1).size - 1) := by
            by_contra x
            have even : Even (n + 1) := by
              have : Even (2 ^ ((n + 1).size - 1)) := by
                refine (even_pow' ?_).mpr ?_
                · exact sub_ne_zero_of_lt (lt_of_add_left_lt n1size_ge_3)
                · exact even_iff.mpr rfl
              simp [←x] at this
              exact this
            have odd : Odd (n + 1) := by
              have : Even (2 ^ (n.size - 1)) := by
                refine (even_pow' ?_).mpr ?_
                · exact sub_ne_zero_of_lt (lt_of_add_left_lt nsize_ge_3)
                · exact even_iff.mpr rfl
              replace : Even n := by simp [←n_is_pow2] at this ; exact this
              replace : Odd (n + 1) := by exact Even.add_one this
              exact this
            replace odd : ¬Even (n + 1) := by exact not_even_iff_odd.mpr odd
            exact absurd even odd
          have n2_ne_pow2 : ¬n + 2 = 2 ^ ((n + 2).size - 1) := by
            by_contra x
            rw (occs := .pos [2]) [n_is_pow2] at x
            have : (2 ^ (n.size - 1) + 2).size = n.size - 1 + 1 := by
              refine size_add ?_ ?_
              · exact Nat.zero_lt_two
              · refine size_le.mp ?_
                · simp [size2_eq_2]
                  exact le_sub_one_of_lt nsize_ge_3
            simp [this] at x
            simp [←n_is_pow2] at x
          have n1size_eq_nsize : (n + 1).size = n.size := same_n1size_iff_not_pow2.mp n1_ne_pow2
          have n2size_eq_nsize : (n + 2).size = n.size := by
            exact same_n1size_iff_not_pow2'.mp ⟨n2_ne_pow2, n1_ne_pow2⟩
          rw [segment]
          split <;> expose_names ; simp [n1size_eq_nsize, n2size_eq_nsize]
          · refine Nat.pow_le_pow_of_le ?_ ?_
            · exact Nat.one_lt_two
            · exact sub_le_succ_sub n.size 2
          · simp [n1size_eq_nsize, n2size_eq_nsize]
            by_cases segment_arg_eq_0 : n - (2 ^ (n.size - 1) - 1) = 0
            · simp [segment_arg_eq_0]
              rw [pow2_nsize_minus_1_divide]
              exact Nat.add_le_add_iff_left.mpr (Nat.one_le_two_pow)
            · rename' segment_arg_eq_0 => segment_arg_pos
              replace segment_arg_pos : n - (2 ^ (n.size - 1) - 1) > 0 := by
                exact zero_lt_of_ne_zero segment_arg_pos
              replace segment_arg_pos :
                  n - (2 ^ (n.size - 1) - 1) = 1 ∨  n - (2 ^ (n.size - 1) - 1) > 1 := by
                exact LE.le.eq_or_lt' segment_arg_pos
              rcases segment_arg_pos with segment_arg_eq_1|segment_arg_ge_2
              · simp [segment_arg_eq_1]
                simp [pow2_nsize_minus_1_divide]
                exact le_pow (zero_lt_sub_of_lt nsize_ge_3)
              · replace segment_arg_ge_2 : n - (2 ^ (n.size - 1) - 1) ≥ 2 := segment_arg_ge_2
                have arg1 : n - (2 ^ (n.size - 1) - 1) < n := by
                  refine sub_lt ?_ ?_
                  · exact zero_lt_of_lt n_ge_4
                  · refine zero_lt_sub_of_lt ?_
                    · refine Nat.one_lt_two_pow ?_
                      · have : n.size - 1 ≥ 2 := by exact le_sub_one_of_lt nsize_ge_3
                        exact Nat.ne_zero_of_lt this
                replace ih := ih (n - (2 ^ (n.size - 1) - 1)) arg1 segment_arg_ge_2
                have : 2 ^ (n.size - 2) + 2 ^ ((n - (2 ^ (n.size - 1) - 1) + 1).size - 1) ≤
                    2 ^ (n.size - 1) := by
                  have s1 : 2 ^ (n.size - 2) + 2 ^ (n.size - 2) = 2 ^ (n.size - 1) := by
                    exact id (Eq.symm pow2_nsize_minus_1_divide)
                  rw (occs := .pos [2]) [←s1]
                  replace s1 : 2 ^ ((n - (2 ^ (n.size - 1) - 1) + 1).size - 1) ≤ 2 ^ (n.size - 2) := by
                    simp [←n_is_pow2]
                    have : n - (n - 1) + 1 = 2 := by
                      refine Eq.symm (Nat.eq_add_of_sub_eq ?_ ?_)
                      · exact NeZero.one_le
                      · simp ; exact Eq.symm (Nat.sub_sub_self (one_le_of_lt n_ge_4))
                    simp [this]
                    exact le_pow (zero_lt_sub_of_lt nsize_ge_3)
                  exact Nat.add_le_add_iff_left.mpr s1
                exact add_le_of_add_le_left this ih
          · intro x
            simp [x] at n_ge_4
        · rename' n_is_pow2 => n_ne_pow2
          by_cases n1_is_pow2 : n + 1 = 2 ^ ((n + 1).size - 1)
          · have n2_ne_pow2 : ¬n + 2 = 2 ^ ((n + 2).size - 1) := by
              by_contra x
              have odd : Odd (n + 2) := by
                have : 2 = 1 + 1 := by exact rfl
                simp only [this, ←add_assoc]
                replace : Even (2 ^ ((n + 1).size - 1)) := by
                  refine (even_pow' ?_).mpr ?_
                  · exact sub_ne_zero_of_lt (lt_of_add_left_lt n1size_ge_3)
                  · exact even_iff.mpr rfl
                simp [←n1_is_pow2] at this
                exact Even.add_one this
              have even : Even (n + 2) := by
                have : Even (2 ^ ((n + 2).size - 1)) := by
                  refine (even_pow' ?_).mpr ?_
                  · exact sub_ne_zero_of_lt (lt_of_add_left_lt n2size_ge_3)
                  · exact even_iff.mpr rfl
                simp [←x] at this
                exact this
              replace even : ¬Odd (n + 2) := by exact not_odd_iff_even.mpr even
              apply absurd odd even
            rw [segment]
            · simp
              split <;> expose_names
              · replace h : n + 2 = 2 ^ ((n + 2).size - 1) - 2 + 2 := by
                  exact congrFun (congrArg HAdd.hAdd h) 2
                have : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
                  refine Nat.sub_add_cancel ?_
                  · exact le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_ge_3))
                simp [this] at h
                exact absurd h n2_ne_pow2
              · have n1size_eq_nsize_add_1 : (n + 1).size = n.size + 1 := by
                  exact increase_n1size_iff_pow2.mpr n1_is_pow2
                have n2size_eq_nsize_add_1 : (n + 2).size = n.size + 1 := by
                  exact increase_n2size_if_pow2₁ n_ge_4 n1_is_pow2
                simp [n1size_eq_nsize_add_1, n2size_eq_nsize_add_1] at *
                simp [←n1_is_pow2]
                exact n_ge_subenvelope (one_le_of_lt n_ge_4)
            · intro n_eq_0 ; simp [n_eq_0] at n_ge_4
          · rename' n1_is_pow2 => n1_ne_pow2
            by_cases n2_is_pow2 : n + 2 = 2 ^ ((n + 2).size - 1)
            · have n1size_eq_nsize : (n + 1).size = n.size := same_n1size_iff_not_pow2.mp n1_ne_pow2
              have n2size_eq_nsize_add_1 : (n + 2).size = n.size + 1 := by
                exact increase_n2size_if_pow2₂ n_ge_4 n2_is_pow2
              rw [segment.eq_def]
              split <;> expose_names
              · simp [size]
              · split <;> expose_names
                · simp [n1size_eq_nsize, n2size_eq_nsize_add_1] at *
                · simp [←n2_is_pow2] at h_1
            · rename' n2_is_pow2 => n2_ne_pow2
              rw [segment.eq_def]
              split <;> expose_names
              · simp [size]
              · split <;> expose_names
                · rw (occs := .pos [1]) [h_1] at n2_ne_pow2
                  have : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
                    exact Nat.sub_add_cancel (le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_ge_3)))
                  simp [this] at n2_ne_pow2
                · simp
                  have n1size_eq_nsize : (n + 1).size = n.size := by
                    exact same_n1size_iff_not_pow2.mp n1_ne_pow2
                  have n2size_eq_nsize : (n + 2).size = n.size := by
                    refine same_n1size_iff_not_pow2'.mp ?_
                    · constructor
                      · exact n2_ne_pow2
                      · exact n1_ne_pow2
                  simp [n1size_eq_nsize, n2size_eq_nsize] at *
                  have arg1 : (n - (2 ^ (n.size - 1) - 1)) < n := by
                    refine sub_lt ?_ ?_
                    · exact zero_lt_of_ne_zero h
                    · refine zero_lt_sub_of_lt ?_
                      · refine Nat.one_lt_two_pow ?_
                        · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt nsize_ge_3)
                  have arg2 : 2 ≤ (n - (2 ^ (n.size - 1) - 1)) := by
                    have s1 : 2 ^ (n.size - 1) ≤ n := n_lower (zero_lt_of_ne_zero h)
                    replace s1 : 2 ^ (n.size - 1) < n := by
                      exact Nat.lt_of_le_of_ne s1 fun a ↦ n_ne_pow2 (id (Eq.symm a))
                    replace s1 : 2 ^ (n.size - 1) + 1 ≤ n := s1
                    refine le_sub_of_add_le ?_
                    · have : 2 + (2 ^ (n.size - 1) - 1) = 2 ^ (n.size - 1) + 1 := by
                        refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add' h).mp) ?_ rfl)
                        · exact AtLeastTwo.prop
                      simp [this]
                      exact s1
                  replace ih := ih (n - (2 ^ (n.size - 1) - 1)) arg1 arg2
                  have s1 :
                      2 ^ (n.size - 2) + 2 ^ ((n - (2 ^ (n.size - 1) - 1) + 1).size - 1) ≤
                      2 ^ (n.size - 1) := by
                    have : 2 ^ (n.size - 1) = 2 ^ (n.size - 2) + 2 ^ (n.size - 2) := by
                      have : n.size - 1 = n.size - 2 + 1 := by
                        refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
                        · exact le_sub_one_of_lt (lt_of_add_left_lt nsize_ge_3)
                      simp [this]
                      exact two_pow_succ (n.size - 2)
                    rw (occs := .pos [2]) [this]
                    refine Nat.add_le_add_iff_left.mpr ?_
                    · replace : n - (2 ^ (n.size - 1) - 1) + 1 = n - 2 ^ (n.size - 1) + 2 := by
                        sorry
                      simp [this]
                      clear this ih arg1 arg2 h n1size_eq_nsize n2size_eq_nsize n1size_ge_3 n2size_ge_3
                      have s1 : n < 2 ^ n.size := by exact lt_size_self n

                      --
                      sorry
                  exact add_le_of_add_le_left s1 ih
              -- Proof Strcture
              -- +1: n ≤ 3 の場合を個別撃破(n = 2 ∨ n = 3)
              -- -1: n ≥ 4
              --    +c0: (n + 0).is_pow2
              --     have : ¬(n + 1).is_pow2 ∧ ¬(n + 0).is_pow2
              --     split
              --    -c0: ¬(n + 0).is_pow2
              --      +c1: (n + 1).is_pow2
              --        have : ¬(n + 2).is_pow2
              --        simplify
              --      -c1: ¬(n + 1).is_pow2
              --        +c2: (n + 2).is_pow2
              --          split
              --        -c2: (n + 2).is_pow2
              --*         split
