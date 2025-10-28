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
-- open LubySegment
-- abbrev segment := LubySegment.segment

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
                · have : size 2 = 2 := by exact size2_eq_2
                  simp [this]
                  exact le_sub_one_of_lt nsize_ge_3
            simp [this] at x
            simp [←n_is_pow2] at x
          have n1size_eq_nsize : (n + 1).size = n.size := by
            exact same_size_iff_not_pow2.mp n1_ne_pow2
          have n2size_eq_nsize : (n + 2).size = n.size := by
            refine same_size_iff_not_pow2'.mp ?_
            · constructor
              · exact n2_ne_pow2
              · exact n1_ne_pow2
          rw [segment]
          split <;> expose_names ; simp [n1size_eq_nsize, n2size_eq_nsize]
          · refine Nat.pow_le_pow_of_le ?_ ?_
            · exact Nat.one_lt_two
            · exact sub_le_succ_sub n.size 2
          · simp [n1size_eq_nsize, n2size_eq_nsize]
            -- 帰納法を使いたいがm ≥ 2 の条件が邪魔をする
            -- n - (2 ^ (n.size - 1) - 1) の場合分けが必要
            by_cases segment_arg_eq_0 : n - (2 ^ (n.size - 1) - 1) = 0
            · simp [segment_arg_eq_0]
              rw [pow2_nsize_minus_1_divide]
              refine Nat.add_le_add_iff_left.mpr ?_
              · exact Nat.one_le_two_pow
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
              · replace segment_arg_ge_2 : n - (2 ^ (n.size - 1) - 1) ≥ 2 := by
                  exact segment_arg_ge_2
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
                  have lower : 2 ^ (n.size - 1) ≤ n := by exact Nat.le_of_eq (id (Eq.symm n_is_pow2))
                  have lower' : 2 ^ (n.size - 2) < n := by
                    have : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 1) := by
                      have s1 : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 2 + 1) := by
                        exact Eq.symm Nat.pow_succ'
                      have s2 : n.size - 2 + 1 = n.size - 1 := by
                        refine Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) ?_)
                        · refine Eq.symm (Nat.sub_add_cancel ?_)
                          · exact le_of_add_left_le nsize_ge_3
                      simp [s2] at s1
                      exact s1
                    simp [←this] at lower
                    rw [mul_comm, mul_two] at lower
                    replace : 0 < 2 ^ (n.size - 2) := by exact Nat.two_pow_pos (n.size - 2)
                    replace : 1 ≤ 2 ^ (n.size - 2) := by exact this
                    replace : 2 ^ (n.size - 2) + 1 ≤ n := by
                      exact add_le_of_add_le_left lower this
                    exact this
                  have upper : n < 2 ^ n.size := by exact lt_size_self n
                  replace s1 : 2 ^ ((n - (2 ^ (n.size - 1) - 1) + 1).size - 1) ≤ 2 ^ (n.size - 2) := by
                    simp [←n_is_pow2]
                    have : n - (n - 1) + 1 = 2 := by
                      refine Eq.symm (Nat.eq_add_of_sub_eq ?_ ?_)
                      · exact NeZero.one_le
                      · simp
                        refine Eq.symm (Nat.sub_sub_self ?_)
                        · exact one_le_of_lt n_ge_4
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
            simp
            split <;> expose_names
            /-
            · replace h : n + 2 = 2 ^ ((n + 2).size - 1) := by
                have s1 : n + 2 = 2 ^ ((n + 2).size - 1) - 2 + 2 := by
                  exact congrFun (congrArg HAdd.hAdd h) 2
                have s2 : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
                  refine Nat.sub_add_cancel ?_
                  · exact le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_ge_3))
            -/
            sorry
            sorry
            sorry
          · rename' n1_is_pow2 => n1_ne_pow2
            by_cases n2_is_pow2 : n + 2 = 2 ^ ((n + 2).size - 1)
            · sorry
            · sorry
        -- Proof Strcture
        -- +1: n ≤ 3 の場合を個別撃破(n = 2 ∨ n = 3)
        -- -1: n ≥ 4
        --    +c0: (n + 0).is_pow2
        --     have : ¬(n + 1).is_pow2 ∧ ¬(n + 0).is_pow2
        --     split
        --*   -c0: ¬(n + 0).is_pow2
        --     +c1: (n + 1).is_pow2
        --       have : ¬(n + 2).is_pow2
        --       split
        --     -c1: ¬(n + 1).is_pow2
        --       +c2: (n + 2).is_pow2
        --         split
        --       -c2: (n + 2).is_pow2
        --         split
/-
        by_cases n2size_eq_n1_size : (n + 2).size = (n + 1).size
        · rw [segment]
          have n2_ne_pow2 : ¬n + 2 = 2 ^ ((n + 2).size - 1) := by
            exact same_size_iff_not_pow2.mpr n2size_eq_n1_size
          split <;> expose_names
          · simp [n2size_eq_n1_size] at * ; exact le.intro (id (Eq.symm pow2_n2_minus_1_divide))
          · -- 場合分けが必要
            have s1 : n - (2 ^ ((n + 1).size - 1) - 1) < n := by
              simp only [n2size_eq_n1_size] at *
              refine sub_lt ?_ ?_
              · exact zero_lt_of_lt n_ge_4
              · refine zero_lt_sub_of_lt ?_
                · refine Nat.one_lt_two_pow ?_
                  · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)
            -- by_cases
            have s2 : 2 ≤ n - (2 ^ ((n + 1).size - 1) - 1) := by
              sorry
            have ih' := ih (n - (2 ^ ((n + 1).size - 1) - 1)) s1 s2
            have s3 : n - (2 ^ ((n + 1).size - 1) - 1) + 1 = n - 2 ^ ((n + 1).size - 1) + 2 := by
              refine Nat.add_left_inj.mpr ?_
              · sorry
            sorry
          · intro x
            replace n_ge_4 : ¬n = 0 := by exact Nat.ne_zero_of_lt n_ge_4
            exact absurd x n_ge_4
        · rw [segment]
          replace n2size_eq_n1_size : (n + 2).size = (n + 1).size + 1 := by
            sorry
          simp [n2size_eq_n1_size] at *
          split <;> expose_names
          · exact Nat.le_refl (2 ^ ((n + 1).size - 1))
          · sorry
          · intro x
            replace n_ge_4 : ¬n = 0 := by exact Nat.ne_zero_of_lt n_ge_4
            exact absurd x n_ge_4
-/

