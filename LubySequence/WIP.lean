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

attribute [local simp] binaryRec

/--
For positions not at envelope boundaries, the segment length remains invariant under
the recursive step: `segment_length (n - (2 ^ ((n + 2).size - 1) - 1)) = segment_length n`.
This shows that within an envelope level, all segments have the same length, which only
increases when crossing to a new envelope.
-/
theorem segment_length_prop2 : ∀ n > 0, ¬segment n = 2 ^ ((n + 1).size - 1) →
    segment_length n = segment_length (n - (2 ^ ((n + 1).size - 1) - 1)) := by
  intro n n_gt_0 n_ne_envelope_segment
  have nsize_add1_minus1 : n.size - 1 + 1 = n.size := by
    refine Nat.sub_add_cancel ?_
    · have s1 : n ≥ 1 := by exact n_gt_0
      replace s1 : n.size ≥ (1 : ℕ).size := by exact size_le_size n_gt_0
      have s2 : (1 : ℕ).size = 1 := by simp [size]
      simp [s2] at s1
      exact s1
  have nsize_divide : 2 ^ n.size = 2 ^ (n.size - 1) * 2 := by
    refine Eq.symm (Nat.pow_pred_mul ?_)
    · exact size_pos.mpr n_gt_0
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have n_ge_3 : n ≥ 3 := by
      replace n_gt_0 : n = 1 ∨ n > 1 := by exact LE.le.eq_or_lt' n_gt_0
      rcases n_gt_0 with eq|n_gt_1
      · simp [eq] at n_ne_envelope_segment
      · replace n_gt_1 : n ≥ 2 := by exact n_gt_1
        replace n_gt_1 : n = 2 ∨ n > 2 := by exact LE.le.eq_or_lt' n_gt_1
        rcases n_gt_1 with eq|n_gt_2
        · simp [eq, segment] at n_ne_envelope_segment
        · replace n_gt_2 : n ≥ 3 := by exact n_gt_2
          exact n_gt_2
    have n2size_gt_3 : (n + 2).size ≥ 3 := by
      have s1 : n + 2 ≥ 3 + 2 := by exact Nat.add_le_add_right n_ge_3 2
      replace s1 : (n + 2).size ≥ (3 + 2).size := by exact size_le_size s1
      have s2 : (3 + 2).size = 3 := by simp [size]
      simp [s2] at s1
      exact s1
    have n_ne_envelope : ¬n = 2 ^ ((n + 2).size - 1) - 2 := by
      by_contra n_is_envelope
      have n_is_envelope' : n + 2 = 2 ^ ((n + 2).size - 1) := by
        refine Eq.symm (Nat.eq_add_of_sub_eq ?_ (id (Eq.symm n_is_envelope)))
        · exact le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_gt_3))
      have n_gt_4 : n ≥ 4 := by
        replace n_ge_3 : n = 3 ∨ n > 3 := by exact LE.le.eq_or_lt' n_ge_3
        rcases n_ge_3 with eq|gt
        · simp [eq, size] at n_is_envelope'
        · exact (by exact gt : n ≥ 4)
      have n1size_eq_nsize : (n + 1).size = n.size := by
        have cond : ¬n + 1 = 2 ^ ((n + 1).size - 1) := by
          have n1 : n + 1 = 2 ^ ((n + 2).size - 1) - 1 := by
            exact Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) (id (Eq.symm n_is_envelope')))
          simp [n1]
          have : (2 ^ ((n + 2).size - 1) - 1).size = (n + 2).size - 1 := by
            exact size_sub (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_gt_3)) Nat.one_pos Nat.one_le_two_pow
          simp [this]
          by_contra odd_and_even
          have even : Even (2 ^ ((n + 2).size - 1 - 1)) := by
            exact (even_pow' (Nat.sub_ne_zero_iff_lt.mpr (lt_sub_of_add_lt n2size_gt_3))).mpr (even_iff.mpr rfl)
          have odd : Odd (2 ^ ((n + 2).size - 1) - 1) := by
            refine Nat.Even.sub_odd Nat.one_le_two_pow ?_ (odd_iff.mpr rfl)
            · refine (even_pow' ?_).mpr (even_iff.mpr rfl)
              · refine Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_gt_3)
          simp [odd_and_even] at odd
          replace odd : ¬Even (2 ^ ((n + 2).size - 1 - 1)) := by exact not_even_iff_odd.mpr odd
          exact absurd even odd
        replace cond : ¬n + 1 = 2 ^ n.size := by
          have n1 : n + 1 = 2 ^ ((n + 2).size - 1) - 1 := by
            exact Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) (id (Eq.symm n_is_envelope')))
          simp [n1]
          have : n + 1 + 1 = 2 ^ ((n + 2).size - 1) - 1 + 1 := congrFun (congrArg HAdd.hAdd n1) 1
          replace : n + 1 + 1 = 2 ^ ((n + 2).size - 1) := by exact n_is_envelope'
          simp [←this]
          by_contra odd_and_even
          have even : Even (n + 2) := by
            have : Even (2 ^ ((n + 2).size - 1)) := by
              refine (even_pow' ?_).mpr ?_
              · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_gt_3)
              · exact even_iff.mpr rfl
            simp [←n_is_envelope'] at this
            exact this
          have odd : ¬Even (n + 2) := by
            have : Even (n + 1) := by
              have : Even (2 ^ n.size) := by
                refine (even_pow' ?_).mpr ?_
                · exact Nat.ne_zero_iff_zero_lt.mpr (size_pos.mpr n_gt_0)
                · exact even_iff.mpr rfl
              simp [←odd_and_even] at this
              exact this
            replace : Odd (n + 1 + 1) := Even.add_one this
            simp at this
            exact not_even_iff_odd.mpr this
          exact absurd even odd
        exact same_n1size_iff_not_pow2.mp cond
      simp [n1size_eq_nsize] at n_ne_envelope_segment
      have : segment n = 2 ^ (n.size - 1) := by
        refine segment_prop1 ?_
        · have n2size_eq_nsize : (n + 2).size = n.size + 1 := by
            have s1 : n.size = (2 ^ ((n + 2).size - 1) - 2).size := congrArg size n_is_envelope
            have s2 : (2 ^ ((n + 2).size - 1) - 2).size = (n + 2).size - 1 := by
              refine size_sub ?_ ?_ ?_
              · exact zero_lt_sub_of_lt (lt_of_add_left_lt n2size_gt_3)
              · exact Nat.zero_lt_two
              · exact le_pow (zero_lt_sub_of_lt (lt_sub_of_add_lt n2size_gt_3))
            simp [s2] at s1
            exact Nat.eq_add_of_sub_eq (one_le_of_lt n2size_gt_3) (id (Eq.symm s1))
          simp [n2size_eq_nsize] at n_is_envelope'
          exact Nat.eq_sub_of_add_eq n_is_envelope'
      exact absurd this n_ne_envelope_segment
    have n2_ne_pow2 : ¬n + 2 = 2 ^ n.size := by
      by_contra x
      have x' : n = 2 ^ n.size - 2 := Nat.eq_sub_of_add_eq x
      simp [x] at n_ne_envelope
      rw [size_pow] at n_ne_envelope
      simp at n_ne_envelope
      exact absurd x' n_ne_envelope
    simp [segment_length]
    rw (occs := .pos [1]) [segment]
    · split
      · expose_names
        exact absurd h n_ne_envelope
      · expose_names
        simp
        have n_ne_envelope' : ¬n + 2 = 2 ^ ((n + 2).size - 1) := by
          have s1 : ¬n + 2 = 2 ^ ((n + 2).size - 1) - 2 + 2 := by
            exact (add_ne_add_left 2).mpr n_ne_envelope
          have s2 : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
            exact Nat.sub_add_cancel (le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_gt_3)))
          simp [s2] at s1
          exact s1
        replace n_ge_3 : n = 3 ∨ n > 3 := by exact LE.le.eq_or_lt' n_ge_3
        rcases n_ge_3 with n_eq_3|n_ge_4
        · simp [n_eq_3] at *
          simp [size, trailing_zeros]
        · replace n_ge_4 : n ≥ 4 := by exact n_ge_4
          have n_ge_7 : n ≥ 7 := by
            have n_lower : n = 4 ∨ n > 4 := by exact LE.le.eq_or_lt' n_ge_4
            rcases n_lower with eq|gt
            · simp [eq, segment, size] at n_ne_envelope_segment
            · replace gt : n ≥ 5 := by exact gt
              replace n_lower : n = 5 ∨ n > 5 := by exact LE.le.eq_or_lt' gt
              rcases n_lower with eq|gt
              · simp [eq, segment, size] at n_ne_envelope_segment
              · replace gt : n ≥ 6 := by exact gt
                replace n_lower : n = 6 ∨ n > 6 := by exact LE.le.eq_or_lt' gt
                rcases n_lower with eq|gt
                · simp [eq, segment, size] at n_ne_envelope_segment
                · replace gt : n ≥ 7 := by exact gt
                  exact gt
          clear n_ge_4
          replace n_ge_7 : n = 7 ∨ n > 7 := by exact LE.le.eq_or_lt' n_ge_7
          rcases n_ge_7 with n_eq_7|n_ge_8
          · simp [n_eq_7, size, trailing_zeros]
          · replace n_ge_8 : n ≥ 8 := by exact n_ge_8
            have nsize_ge_4 : n.size ≥ 4 := by
              have s1 : n.size ≥ (8 : ℕ).size := by exact size_le_size n_ge_8
              have s2 : (8 : ℕ).size = 4 := by simp [size]
              simp [s2] at s1
              exact s1
            have n1size_ge_4 : (n + 1).size ≥ 4 := by
              have : (n + 1).size ≥ n.size := size_le_size (Nat.le_add_right n 1)
              exact Nat.le_trans nsize_ge_4 this
            by_cases at_seg_beg : n + 1 = 2 ^ ((n + 1).size - 1)
            · have n1size_eq_nsize_add_1 : (n + 1).size = n.size + 1 := by
                have s1 : n = 2 ^ ((n + 1).size - 1) - 1 := Nat.eq_sub_of_add_eq at_seg_beg
                replace s1 : n.size = (2 ^ ((n + 1).size - 1) - 1).size := congrArg size s1
                have : (2 ^ ((n + 1).size - 1) - 1).size = (n + 1).size - 1 := by
                  refine size_sub ?_ ?_ ?_
                  · refine zero_lt_sub_of_lt ?_
                    · refine one_lt_iff_ne_zero_and_ne_one.mpr ?_
                      · constructor
                        · refine Nat.ne_zero_iff_zero_lt.mpr ?_
                          · refine size_pos.mpr ?_
                            · exact Nat.add_pos_left n_gt_0 1
                        · exact Ne.symm (Nat.ne_of_lt (lt_of_add_left_lt n1size_ge_4))
                  · exact Nat.one_pos
                  · exact Nat.one_le_two_pow
                simp [this] at s1
                exact (Nat.sub_eq_iff_eq_add (one_le_of_lt n1size_ge_4)).mp (id (Eq.symm s1))
              have n2size_eq_nsize_add_1 : (n + 2).size = n.size + 1 := by
                have : n + 1 + 1 = 2 ^ ((n + 1).size - 1) + 1 := by
                  exact congrFun (congrArg HAdd.hAdd at_seg_beg) 1
                replace : (n + 1 + 1).size = (2 ^ ((n + 1).size - 1) + 1).size := congrArg size this
                simp [n1size_eq_nsize_add_1] at this
                replace s1 : (2 ^ n.size + 1).size = n.size + 1 := by
                  refine size_add ?_ ?_
                  · exact Nat.one_pos
                  · exact Nat.one_lt_two_pow (Nat.ne_zero_of_lt nsize_ge_4)
                simp [s1] at this
                exact this
              simp [n2size_eq_nsize_add_1, n1size_eq_nsize_add_1] at *
              have : n - (2 ^ n.size - 1) = 0 := by
                exact Nat.sub_eq_zero_of_le (le_sub_of_add_le (Nat.le_of_eq at_seg_beg))
              simp [this]
              rw [add_comm]
              have : trailing_zeros (1 + 2 ^ (n.size - 1)) = trailing_zeros 1 := by
                refine trailing_zeros_prop7 (n.size - 1) 1 ?_ ?_
                · exact Nat.one_lt_two_pow (Nat.sub_ne_zero_iff_lt.mpr n2size_gt_3)
                · exact Nat.one_ne_zero
              simp [this]
            · have n1size_eq_nsize : (n + 1).size = n.size := by
                have : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := by exact size_limit n
                rcases this with eq|add1
                · exact eq
                · have n_ne_pow2 : ¬n = 2 ^ (n.size - 1) := by
                    by_contra x
                    replace x : (n + 1).size = (2 ^ (n.size - 1) + 1).size := by simp [←x]
                    replace x : (n + 1).size = n.size := by
                      have : (2 ^ (n.size - 1) + 1).size = n.size - 1 + 1 := by
                        refine size_add ?_ ?_
                        · exact Nat.one_pos
                        · exact
                            Nat.one_lt_two_pow (Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt nsize_ge_4))
                      simp [this] at x
                      replace : n.size - 1 + 1 = n.size := by grind
                      simp [this] at x
                      exact x
                    simp [x] at add1
                  refine same_n1size_iff_not_pow2.mp ?_
                  · simp [add1] at at_seg_beg
                    exact at_seg_beg
              have n1_ne_pow2 : ¬n + 1 = 2 ^ n.size := same_n1size_iff_not_pow2.mpr n1size_eq_nsize
              have n2size_eq_nsize : (n + 2).size = n.size := by
                have : (n + 2).size = (n + 1).size := by
                  by_contra x
                  have : n + 1 + 1 = 2 ^ (n + 1).size := by
                    refine increase_n1size_at_pow2 ?_
                    · have : (n + 2).size = (n + 1).size ∨ (n + 2).size = (n + 1).size + 1 := by
                        exact size_limit (n + 1)
                      rcases this with eq|gt
                      · exact absurd eq x
                      · exact gt
                  replace : n + 2 = 2 ^ (n + 1).size := this
                  simp [this] at n_ne_envelope'
                  rw [size_pow] at n_ne_envelope'
                  replace : (n + 1).size + 1 - 1 = (n + 1).size := rfl
                  simp [this] at n_ne_envelope'
                simp [this]
                exact n1size_eq_nsize
              rw [segment.eq_def] at n_ne_envelope_segment
              split at n_ne_envelope_segment
              · contradiction
              · split at n_ne_envelope_segment <;> expose_names
                · simp [n1size_eq_nsize, n2size_eq_nsize] at *
                  exact absurd h_2 n_ne_envelope
                · simp at n_ne_envelope_segment
                  simp [n1size_eq_nsize, n2size_eq_nsize] at *
                  by_cases eq : 2 ^ (n.size - 1) = n
                  · simp [eq]
                    have : n - (n - 1) = 1 := by exact Nat.sub_sub_self n_gt_0
                    simp [this]
                    have : trailing_zeros (2 ^ (n.size - 2) + 2) = trailing_zeros 2 := by
                      rw [add_comm]
                      refine trailing_zeros_prop1' 2 ?_ (n.size - 2) ?_
                      · exact Nat.zero_lt_two
                      · refine size_le.mp ?_
                        · refine le_sub_of_add_le ?_
                          · simp ; exact nsize_ge_4
                    simp [this]
                  · rename' eq => n_ne_pow2
                    have s2 : segment (2 ^ (n.size - 2)) ≤ 2 ^ ((2 ^ (n.size - 2) + 1).size - 1) := by
                      exact segment_limit2 (le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_gt_3)))
                    have s3 : (2 ^ (n.size - 2) + 1).size = n.size - 2 + 1 := by
                       refine size_add ?_ ?_
                       · exact Nat.one_pos
                       · refine Nat.one_lt_two_pow_iff.mpr ?_
                         · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_gt_3)
                    simp [s3] at s2
                    have n_lt_pow2_minus_2 : n < 2 ^ n.size - 2 := by
                      have : n < 2 ^ n.size := lt_size_self n
                      replace : n ≤ 2 ^ n.size - 1 := le_sub_one_of_lt this
                      replace : n = 2 ^ n.size - 1 ∨ n < 2 ^ n.size - 1 := Nat.eq_or_lt_of_le this
                      rcases this with eq|lt
                      · replace eq : n + 1 = 2 ^ n.size := by
                          refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?_ (id (Eq.symm eq)))
                          · exact Nat.one_le_two_pow
                        exact absurd eq n1_ne_pow2
                      · replace lt : n ≤ 2 ^ n.size - 1 - 1 := by exact le_sub_one_of_lt lt
                        replace lt : n ≤ 2 ^ n.size - 2 := by grind
                        replace lt : n = 2 ^ n.size - 2 ∨ n < 2 ^ n.size - 2 := Nat.eq_or_lt_of_le lt
                        rcases lt with eq|lt
                        · replace eq : n + 2 = 2 ^ n.size := by
                            refine Eq.symm (Nat.eq_add_of_sub_eq ?_ (id (Eq.symm eq)))
                            · exact le_pow (size_pos.mpr n_gt_0)
                          exact absurd eq n2_ne_pow2
                        · exact lt
                    -- ここまでOK
                    have peel_segment : segment (n / 2 - 1) ≤ 2 ^ (n.size - 2) := by
                      have s1 : segment (n / 2 - 1) ≤ 2 ^ ((n / 2 - 1 + 1).size - 1) := by
                        refine segment_limit2 ?_
                        · refine le_sub_one_of_lt ?_
                          · replace : 2 < n / 2 := by
                              refine (Nat.lt_div_iff_mul_lt ?_).mpr ?_
                              · exact Nat.zero_lt_two
                              · simp ; grind
                            exact this
                      have s4 : n / 2 - 1 + 1 = n / 2 := by
                        refine Nat.sub_add_cancel ?_
                        · refine (Nat.one_le_div_iff ?_).mpr ?_
                          · exact Nat.zero_lt_two
                          · exact le_of_add_left_le n_ge_8
                      simp [s4] at s1
                      replace s4 : (n / 2).size = n.size - 1 := by
                        by_cases even : Even n
                        · exact size_div n_gt_0 (even_iff_two_dvd.mp even)
                        · rename' even => odd
                          replace odd : Odd n := by exact not_even_iff_odd.mp odd
                          have s : ((n - 1) / 2).size = (n - 1).size - 1 := by
                            refine size_div ?_ ?_
                            · exact le_sub_one_of_lt (lt_of_add_left_lt n_ge_8)
                            · refine dvd_of_mod_eq_zero ?_
                              · replace odd : Even (n - 1) := Odd.tsub_odd odd (odd_iff.mpr rfl)
                                exact even_iff.mp odd
                          have right : (n - 1).size = n.size := by
                            sorry
                          have left : ((n - 1) / 2).size = (n / 2).size := by
                            let m := n / 2
                            have m_def : m = value_of% m := rfl
                            have n1_bits : (2 * m).bits = false :: m.bits := by
                              refine bits_of_double_eq_cons_false_and_bits m ?_
                              · exact Nat.lt_of_sub_eq_succ (id (Eq.symm s4))
                            replace n1_bits : (n - 1).bits = false :: m.bits := by
                              have : n - 1 = 2 * m := by grind
                              simp [←this] at n1_bits
                              exact n1_bits
                            replace n1_bits : (n - 1).div2.bits = (n - 1).bits.tail := by
                              exact div2_bits_eq_tail (n - 1)
                            have t1 : (n - 1) / 2 = (n - 1).div2 := by
                              exact Eq.symm (div2_val (n - 1))
                            simp [←t1] at n1_bits
                            -- こんな感じでもっと色々
                            sorry
                          simp [left, right] at s
                          exact s
                      -- 
                      sorry
                    have seg_limit : segment (n - (2 ^ (n.size - 1) - 1)) < 2 ^ (n.size - 2) := by
                      have concept1 : segment (n / 2) ≤ 2 ^ (n.size - 2) := by
                        have s1 : segment (n / 2) ≤ 2 ^ ((n / 2 + 1).size - 1) := by
                          refine segment_limit2 ?_
                          · refine (Nat.le_div_iff_mul_le ?_).mpr ?_
                            · exact Nat.zero_lt_two
                            · exact le_of_add_left_le n_ge_8
                        have : (n / 2 + 1).size ≤ ((2 ^ n.size - 2) / 2 + 1).size := by
                          have : n / 2 < (2 ^ n.size - 2) / 2 := by
                            refine div_lt_div_of_lt_of_dvd ?_ n_lt_pow2_minus_2
                            · refine Nat.dvd_sub ?_ ?_
                              · exact Dvd.intro_left (2 ^ (n.size - 1)) (id (Eq.symm nsize_divide))
                              · exact (minFac_eq_two_iff 2).mp rfl
                          replace : n / 2 + 1 < (2 ^ n.size - 2) / 2 + 1 := Nat.add_lt_add_right this 1
                          exact size_le_size (le_of_succ_le this)
                        have aux : (2 ^ n.size - 2) / 2 + 1 = 2 ^ n.size / 2 := by
                          have : 1 = 2 / 2 := rfl
                          simp only [this]
                          replace : (2 ^ n.size - 2) / 2 + 2 / 2 = (2 ^ n.size - 2 + 2) / 2 := by
                            refine Eq.symm (Nat.add_div_of_dvd_left ?_)
                            · exact (minFac_eq_two_iff 2).mp rfl
                          simp only [this]
                          replace : 2 ^ n.size - 2 + 2 = 2 ^ n.size := by
                            exact Nat.sub_add_cancel (le_pow (size_pos.mpr n_gt_0))
                          simp [this]
                        simp only [aux] at this
                        have x : (2 ^ n.size / 2).size ≤ n.size - 1 := by 
                          sorry
                        have s2 : (n / 2 + 1).size = n.size - 1 := by
                          have : n / 2 < 2 ^ (n.size - 1) := by
                            have : n < 2 ^ n.size := by exact lt_size_self n
                            replace : n < 2 ^ (n.size - 1) * 2 := Nat.lt_of_lt_of_eq this nsize_divide
                            grind
                          replace : n / 2 + 1 ≤ 2 ^ (n.size - 1) := this
                          replace : (n / 2 + 1).size ≤ (2 ^ (n.size - 1)).size := size_le_size this
                          simp [size_pow, nsize_add1_minus1] at this
                          replace : (n / 2 + 1).size = n.size ∨ (n / 2 + 1).size < n.size := by
                            exact Nat.eq_or_lt_of_le this
                          rcases this with eq|lt
                          · sorry
                          · replace lt : (n / 2 + 1).size ≤ (2 ^ (n.size - 1)).size := by
                              apply?
                              refine size_le_size ?_
                              · apply?
                          · replace t1 : n = 2 * (n / 2) := by exact Eq.symm (two_mul_div_two_of_even even)
                            rw (occs := .pos [1]) [t1]
                            simp [←t1]
                            -- exact t2
                            sorry
                          · replace t1 : n = 2 * (n / 2) + 1 := by grind
                            -- rw (occs := .pos [1]) [t1]
                            replace t1 : (2 * (n / 2) + 1).size = (2 * (n / 2)).size := by
                              refine Eq.symm (size_of_even_add_one_eq_size_of_self (n / 2) ?_)
                              · refine Nat.div_pos ?_ ?_
                                · exact le_of_add_left_le n_ge_8
                                · exact Nat.zero_lt_two
                            -- simp [t1, t2]
                            sorry
                        simp [s2] at s1
                        -- exact s1
                        sorry
                      have : n - (2 ^ (n.size - 1) - 1) ≤ n / 2 := by
                        have pow2nsize_halve : 2 ^ n.size = 2 ^ (n.size - 1) * 2 := by
                          exact Eq.symm (Nat.pow_pred_mul (size_pos.mpr n_gt_0))
                        have : n - (2 ^ (n.size - 1) - 1) = n - 2 ^ (n.size - 1) + 1 := by
                          refine tsub_tsub_assoc ?_ ?_
                          · exact n_ge_subenvelope n_gt_0
                          · exact Nat.one_le_two_pow
                        simp [this]
                        sorry
                      replace s1 : segment (n - (2 ^ (n.size - 1) - 1)) ≤ segment (n / 2) := by
                        exact segment_is_monotone' this
                      replace s1 : segment (n - (2 ^ (n.size - 1) - 1)) ≤ 2 ^ (n.size - 2) := by
                        exact Nat.le_trans s1 concept1
                      replace s1 :
                          segment (n - (2 ^ (n.size - 1) - 1)) = 2 ^ (n.size - 2) ∨
                          segment (n - (2 ^ (n.size - 1) - 1)) < 2 ^ (n.size - 2) := by
                        exact Nat.eq_or_lt_of_le s1
                      rcases s1 with eq|gt
                      · simp [eq] at n_ne_envelope_segment
                        rw [←mul_two, ←pow_succ] at n_ne_envelope_segment
                        have : n.size - 2 + 1 = n.size - 1 := by grind
                        simp [this] at n_ne_envelope_segment
                      · exact gt
                    have :
                        trailing_zeros (2 ^ (n.size - 2) + segment (n - (2 ^ (n.size - 1) - 1))) =
                        trailing_zeros (segment (n - (2 ^ (n.size - 1) - 1))) := by
                      rw [add_comm]
                      refine trailing_zeros_prop7 (n.size - 2) (segment (n - (2 ^ (n.size - 1) - 1))) ?_ ?_
                      · exact seg_limit
                        /- have s1 : segment (n - (2 ^ (n.size - 1) - 1)) ≤ n - (2 ^ (n.size - 1) - 1) := by
                          -- envelope_segmentでないことを使ってない
                          refine segment_limit ?_
                          · refine (Nat.le_sub_iff_add_le' ?_).mpr ?_
                            · refine sub_le_of_le_add ?_
                              · have : 2 ^ (n.size - 1) ≤ n := by exact n_ge_subenvelope n_gt_0
                                exact le_add_right_of_le this
                            · refine add_le_of_le_sub ?_ ?_
                              · exact le_of_add_left_le n_ge_8
                              · refine sub_le_of_le_add ?_
                                have : n - 2 + 1 = n - 1 := by
                                  refine Eq.symm (Nat.eq_add_of_sub_eq ?_ rfl)
                                  · refine le_sub_one_of_lt ?_
                                    · exact lt_of_add_left_lt n_ge_8
                                simp [this]
                                have s1 : 2 ^ (n.size - 1) ≤ n := by exact n_ge_subenvelope n_gt_0
                                replace s1 : 2 ^ (n.size - 1) = n ∨ 2 ^ (n.size - 1) < n := by
                                  exact Nat.eq_or_lt_of_le s1
                                rcases s1 with h|h
                                · exact absurd h eq
                                · exact (Nat.le_sub_one_iff_lt n_gt_0).mpr h
                        have s2 : n - (2 ^ (n.size - 1) - 1) < 2 ^ (n.size - 2) := by
                          sorry
                        exact Nat.lt_of_le_of_lt s1 s2
                        -/
                      · exact Nat.ne_zero_iff_zero_lt.mpr (segment_is_pos (n - (2 ^ (n.size - 1) - 1)))
                    simp [this]
    · intro x
      simp [x] at n_ge_3
