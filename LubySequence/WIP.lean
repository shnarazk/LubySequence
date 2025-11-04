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
    replace n_ge : n = 2 ∨ n > 2 := LE.le.eq_or_lt' n_ge
    rcases n_ge with n_eq_2|n_ge
    · simp [n_eq_2, segment]
    · replace n_ge : n = 3 ∨ n > 3 := LE.le.eq_or_lt' n_ge
      rcases n_ge with n_eq_3|n_ge_4
      · simp [n_eq_3, segment, size, binaryRec]
      · replace n_ge_4 : n ≥ 4 := n_ge_4
        have nsize_ge_3 : n.size ≥ 3 := size4_add_0_ge_2 n_ge_4
        have n1size_ge_3 : (n + 1).size ≥ 3 := size4_add_0_ge_2 (le_add_right_of_le n_ge_4)
        have n2size_ge_3 : (n + 2).size ≥ 3 := size2_add_2_ge_2 (le_of_add_left_le n_ge_4)
        have pow2_nsize_divide : 2 ^ n.size = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
          have s1 : 2 ^ n.size = 2 ^ (n.size - 1) * 2 := by
            exact Eq.symm (Nat.pow_pred_mul (zero_lt_of_lt nsize_ge_3))
          simp [s1, mul_two]
        have pow2_nsize_minus_1_divide : 2 ^ (n.size - 1) = 2 ^ (n.size - 2) + 2 ^ (n.size - 2) := by
          have s1 : 2 ^ (n.size - 1) = 2 ^ (n.size - 1 - 1) * 2 := by
            exact Eq.symm (two_pow_pred_mul_two (zero_lt_sub_of_lt (lt_of_add_left_lt nsize_ge_3)))
          have s2 : n.size - 1 - 1 = n.size - 2 := rfl
          simp [s2, mul_two] at s1
          exact s1
        by_cases n_is_pow2 : n = 2 ^ (n.size - 1)
        · have n1_ne_pow2 : ¬n + 1 = 2 ^ n.size := by
            by_contra x
            have even : Even (n + 1) := by
              have : Even (2 ^ n.size) := by
                exact (even_pow' (Nat.ne_zero_of_lt nsize_ge_3)).mpr (even_iff.mpr rfl)
              simp [←x] at this
              exact this
            have odd : Odd (n + 1) := by
              have : Even (2 ^ (n.size - 1)) := by
                refine (even_pow' ?_).mpr ?_
                · exact sub_ne_zero_of_lt (lt_of_add_left_lt nsize_ge_3)
                · exact even_iff.mpr rfl
              replace : Even n := by simp [←n_is_pow2] at this ; exact this
              replace : Odd (n + 1) := Even.add_one this
              exact this
            replace odd : ¬Even (n + 1) := not_even_iff_odd.mpr odd
            exact absurd even odd
          have n2_ne_pow2 : ¬n + 2 = 2 ^ n.size := by
            by_contra x
            replace n_is_pow2 : n * 2 = 2 ^ (n.size - 1) * 2 := by
              exact congrFun (congrArg HMul.hMul n_is_pow2) 2
            have : 2 ^ (n.size - 1) * 2 = 2 ^ (n.size - 1 + 1) := rfl
            simp [this] at n_is_pow2
            replace : n.size - 1 + 1 = n.size := Nat.sub_add_cancel (one_le_of_lt nsize_ge_3)
            simp [this] at n_is_pow2
            simp [←n_is_pow2, mul_two] at x
            simp [←x] at n_ge_4
          have n1size_eq_nsize : (n + 1).size = n.size := by
            refine same_n1size_iff_not_pow2.mp ?_
            · by_contra x 
              have odd : Odd (n + 1) := False.elim (n1_ne_pow2 x)
              have even : Even (n + 1) := by
                have : Even (2 ^ n.size) := False.elim (n1_ne_pow2 x)
                simp [←x] at this
                exact this
              replace odd : ¬Even (n + 1) := not_even_iff_odd.mpr odd
              exact absurd even odd
          have n2size_eq_nsize : (n + 2).size = n.size := by
            exact same_n2size_iff_not_pow2'.mp ⟨n2_ne_pow2, n1_ne_pow2⟩
          rw [segment]
          split <;> expose_names ; simp [n1size_eq_nsize, n2size_eq_nsize]
          · exact Nat.pow_le_pow_of_le (Nat.one_lt_two) (sub_le_succ_sub n.size 2)
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
          by_cases n1_is_pow2 : n + 1 = 2 ^ n.size
          · have n2_ne_pow2 : ¬n + 2 = 2 ^ n.size := by
              by_contra x
              have odd : Odd (n + 2) := by
                have : 2 = 1 + 1 := rfl
                simp only [this, ←add_assoc]
                replace : Even (2 ^ n.size) := by
                  exact (even_pow' (Nat.ne_zero_of_lt nsize_ge_3)).mpr (even_iff.mpr rfl)
                simp [←n1_is_pow2] at this
                exact Even.add_one this
              have even : Even (n + 2) := by
                have : Even (2 ^ n.size) := by
                  exact (even_pow' (Nat.ne_zero_of_lt nsize_ge_3)).mpr (even_iff.mpr rfl)
                simp [←x] at this
                exact this
              replace even : ¬Odd (n + 2) := not_odd_iff_even.mpr even
              apply absurd odd even
            rw [segment]
            · simp
              split <;> expose_names
              · -- have xx : (n + 2).size 
                have n1size_eq_nsize_add_1 : (n + 1).size = n.size + 1 := by
                  exact increase_n1size_iff_pow2.mpr n1_is_pow2
                have n2size_eq_n1size : (n + 2).size = (n + 1).size := by
                  have : n + 1 + 1 = 2 ^ n.size + 1 := congrFun (congrArg HAdd.hAdd n1_is_pow2) 1
                  replace : n + 2 = 2 ^ n.size + 1 := this
                  replace : (n + 2).size = (2 ^ n.size + 1).size := congrArg size this
                  replace : (n + 2).size = n.size + 1 := increase_n2size_if_pow2₁ n_ge_4 n1_is_pow2
                  simp [←n1size_eq_nsize_add_1] at this
                  exact this
                simp [n1size_eq_nsize_add_1, n2size_eq_n1size] at *
                refine Luby.pow2_le_pow2 (n.size - 1) n.size ?_
                · exact sub_le n.size 1
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
                replace n2_is_pow2 : n + 2 - 1 = 2 ^ ((n + 2).size - 1) - 1 := by
                  exact congrFun (congrArg HSub.hSub n2_is_pow2) 1
                replace n2_is_pow2 : n + 1 = 2 ^ ((n + 2).size - 1) - 1 := by exact n2_is_pow2
                replace n2_is_pow2 : (n + 1).size = (2 ^ ((n + 2).size - 1) - 1).size := by
                  exact congrArg size n2_is_pow2
                replace n2_is_pow2 : (n + 1).size = (n + 2).size - 1 := by
                  have : (2 ^ ((n + 2).size - 1) - 1).size = (n + 2).size - 1 := by
                    refine size_sub ?_ ?_ ?_
                    · exact zero_lt_sub_of_lt (lt_of_add_left_lt n2size_ge_3)
                    · exact Nat.one_pos
                    · exact Nat.one_le_two_pow
                  simp [this] at n2_is_pow2
                  exact n2_is_pow2
                simp [n2_is_pow2] at n1size_eq_nsize
                refine (Nat.sub_eq_iff_eq_add ?_).mp n1size_eq_nsize
                · exact one_le_of_lt n2size_ge_3
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
                    by_contra x
                    replace x : (n + 2).size = n.size + 1 := by
                      have : (n + 2).size = (n + 1).size ∨ (n + 2).size = (n + 1).size + 1 := by
                        exact size_limit (n + 1)
                      simp [n1size_eq_nsize] at this
                      rcases this with eq|gt
                      · exact absurd eq x
                      · exact gt
                    have : (n + 2).size = (n + 1).size + 1 := by
                      simp [←n1size_eq_nsize] at x
                      exact x
                    replace : (n + 1 + 1).size = (n + 1).size + 1 := this
                    replace : n + 1 + 1 = 2 ^ (n + 1).size := increase_n1size_iff_pow2.mp this
                    simp [x] at h_1
                    simp [n1size_eq_nsize] at this
                    replace : n + 2 = 2 ^ n.size := this
                    replace : n = 2 ^ n.size - 2 := by exact Nat.eq_sub_of_add_eq this
                    exact absurd this h_1
                  have z : ¬n + 2 = 2 ^ n.size ∧ ¬n + 1 = 2 ^ n.size := by
                    exact same_n2size_iff_not_pow2'.mpr n2size_eq_nsize
                  replace n2_ne_pow2 := z.left
                  simp [n1size_eq_nsize, n2size_eq_nsize] at *
                  -- have : ¬n + 2 = 2 ^ n.size := by apply?
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
                    · -- replace : n - (2 ^ (n.size - 1) - 1) + 1 = n - 2 ^ (n.size - 1) + 2 := by
                      --  have : n - (2 ^ (n.size - 1) - 1) = n - 2 ^ (n.size - 1) + 1 := by
                      --    refine tsub_tsub_assoc ?_ ?_
                      --    · exact n_lower (zero_lt_of_ne_zero h)
                      --    · exact Nat.one_le_two_pow
                      --  simp [this]
                      -- simp [this]
                      clear this ih arg1 arg2 h n1size_eq_nsize n2size_eq_nsize n1size_ge_3 n2size_ge_3
                      have s1 : n < 2 ^ n.size := by exact lt_size_self n
                      replace s1 : n - (2 ^ (n.size - 1) - 1) ≤ 2 ^ n.size - 1 - (2 ^ (n.size - 1) - 1):= by
                        exact Nat.sub_le_sub_right (le_sub_one_of_lt s1) (2 ^ (n.size - 1) - 1)
                      have : 2 ^ n.size = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
                        have : n.size = n.size - 1 + 1 := by
                          exact (Nat.sub_eq_iff_eq_add (one_le_of_lt nsize_ge_3)).mp rfl
                        rw (occs := .pos [1]) [this]
                        exact two_pow_succ (n.size - 1)
                      rw [this] at s1
                      replace : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) - 1 - (2 ^ (n.size - 1) - 1) =
                          2 ^ (n.size - 1) := by
                        have : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) - 1 =
                            2 ^ (n.size - 1) + (2 ^ (n.size - 1) - 1) := by
                          exact Nat.add_sub_assoc (Nat.one_le_two_pow) (2 ^ (n.size - 1))
                        simp [this]
                      rw [this] at s1
                      replace s1 : n - (2 ^ (n.size - 1) - 1) + 1 ≤ 2 ^ (n.size - 1) + 1 := by
                        exact Nat.add_le_add_right s1 1
                      replace s1 : (n - (2 ^ (n.size - 1) - 1) + 1).size ≤ (2 ^ (n.size - 1) + 1).size := by
                        exact size_le_size s1
                      replace : (2 ^ (n.size - 1) + 1).size = n.size := by
                        have t1 : (2 ^ (n.size - 1) + 1).size = n.size - 1 + 1 := by
                          refine size_add Nat.one_pos ?_
                          · refine size_le.mp ?_
                            · simp ; exact le_sub_one_of_lt (lt_of_add_left_lt nsize_ge_3)
                        have t2 : n.size - 1 + 1 = n.size := by grind
                        simp [t2] at t1
                        exact t1
                      simp [this] at s1
                      replace s1 : (n - (2 ^ (n.size - 1) - 1) + 1).size < n.size := by
                        -- n2_ne_pow2 なのだから言えるのでは
                        have : n - (2 ^ (n.size - 1) - 1) + 1 < 2 ^ (n.size - 1) := by
                          replace : n < 2 ^ n.size := by exact lt_size_self n
                          replace : n - 2 ^ (n.size - 1) < 2 ^ n.size - 2 ^ (n.size - 1) := by
                            refine Nat.sub_lt_sub_right ?_ this
                            · refine n_lower ?_
                              · exact zero_lt_of_lt n_ge_4
                          --
                          have aux : 2 ^ n.size - 2 ^ (n.size - 1) = 2 ^ (n.size - 1) := by
                            replace : 2 ^ n.size = 2 ^ (n.size - 1) * 2 := by
                              refine Eq.symm (Nat.pow_pred_mul ?_)
                              · exact zero_lt_of_lt nsize_ge_3
                            simp [this]
                            rw [mul_two]
                            simp
                          simp [aux] at this
                          replace : n - 2 ^ (n.size - 1) + 1 ≤ 2 ^ (n.size - 1) := this
                          replace aux : ¬n - 2 ^ (n.size - 1) + 1 = 2 ^ (n.size - 1) := by 
                            by_contra x
                            replace : n + 1 = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
                              refine Nat.eq_add_of_sub_eq ?_ ?_
                              · have : 2 ^ (n.size - 1) ≤ n := n_lower (zero_lt_of_lt n_ge_4)
                                exact le_add_right_of_le this
                              · rw (occs := .pos [2]) [←x] ; grind
                            replace : n + 1 = 2 ^ n.size := by 
                              have s : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) = 2 ^ n.size := by
                                have s1 : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) = 2 ^ (n.size - 1 + 1) := by
                                  exact Eq.symm (two_pow_succ (n.size - 1))
                                have s2 : n.size - 1 + 1 = n.size := by grind
                                simp [s2] at s1
                                exact s1
                              simp [s] at this
                              exact this
                            simp [this] at n1_ne_pow2
                          --
                          replace :
                              n - 2 ^ (n.size - 1) + 1 = 2 ^ (n.size - 1) ∨
                              n - 2 ^ (n.size - 1) + 1 < 2 ^ (n.size - 1) := by
                            exact Nat.eq_or_lt_of_le this
                          rcases this with eq|gt
                          · exact absurd eq aux
                          · -- さらに深く剥ぎ取ることが必要
                            replace gt : n - 2 ^ (n.size - 1) + 1 + 1 ≤ 2 ^ (n.size - 1) := gt
                            replace gt :
                                n - 2 ^ (n.size - 1) + 1 + 1 = 2 ^ (n.size - 1) ∨
                                n - 2 ^ (n.size - 1) + 1 + 1 < 2 ^ (n.size - 1) := by
                              exact Nat.eq_or_lt_of_le gt
                            rcases gt with eq|gt
                            · have : n + 2 = 2 ^ n.size := by
                                have left : n - 2 ^ (n.size - 1) + 1 + 1 = n - 2 ^ (n.size - 1) + 2 := by
                                  grind
                                simp [left] at eq
                                replace left : n - 2 ^ (n.size - 1) + 2 = n + 2 - 2 ^ (n.size - 1) := by
                                  refine Eq.symm (Nat.sub_add_comm ?_)
                                  · refine n_lower ?_
                                    · exact zero_lt_of_lt n_ge_4
                                simp [left] at eq
                                replace eq : n + 2 = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
                                  refine (Nat.sub_eq_iff_eq_add ?_).mp eq
                                  · have : 2 ^ (n.size - 1) ≤ n := by
                                      refine n_lower ?_
                                      · exact zero_lt_of_lt n_ge_4
                                    exact le_add_right_of_le this
                                simp [←pow2_nsize_divide] at eq
                                exact eq
                              exact absurd this n2_ne_pow2
                            · replace aux : n - (2 ^ (n.size - 1) - 1) = n - 2 ^ (n.size - 1) + 1 := by
                                refine tsub_tsub_assoc ?_ ?_
                                · refine n_lower ?_
                                  · exact zero_lt_of_lt n_ge_4
                                · exact Nat.one_le_two_pow
                              simp [aux]
                              exact gt
                        replace : (n - (2 ^ (n.size - 1) - 1) + 1).size ≤ n.size - 1 := by
                          exact size_le.mpr this
                        replace : (n - (2 ^ (n.size - 1) - 1) + 1).size < n.size - 1 + 1 := by
                          exact Order.lt_add_one_iff.mpr this
                        have it : n.size - 1 + 1 = n.size := by grind
                        simp [it] at this
                        exact this
                      replace s1 : (n - (2 ^ (n.size - 1) - 1) + 1).size ≤ n.size - 1 := by
                        exact le_sub_one_of_lt s1
                      replace s1 : (n - (2 ^ (n.size - 1) - 1) + 1).size - 1 ≤ n.size - 1 - 1 := by
                        exact Nat.sub_le_sub_right s1 1
                      exact
                        Luby.pow2_le_pow2 ((n - (2 ^ (n.size - 1) - 1) + 1).size - 1) (n.size - 2) s1
                  exact add_le_of_add_le_left s1 ih

