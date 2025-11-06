import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Utils
import LubySequence.Basic
import LubySequence.TrailingZeros

/-!
Segments are monotonic subsequences in the Luby sequence.
In this file, it's defined as a mapping from ℕ to ℕ.
But its index starts from 1.
-/

open Nat

namespace LubySegment

-- #eval! List.range 8 |>.map (fun n ↦ (n, 2 ^ (n.size - 1), Luby.S₂ n, Luby.luby n))

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
      have n2size : (n + 2).size ≥ 2 := by exact size0_add_2_ge_2 n
      have order : n - (2 ^ ((n + 2).size - 1) - 1) < n := by
        have s1 : 0 < 2 ^ ((n + 2).size - 1) - 1 := by
          exact zero_lt_sub_of_lt (Nat.one_lt_two_pow (Nat.sub_ne_zero_iff_lt.mpr n2size))
        refine sub_lt ?_ s1
        · by_contra n_eq_0
          simp at n_eq_0
          simp [n_eq_0, size, binaryRec] at h
      2 ^ ((n + 2).size - 2) + segment (n - (2 ^ ((n + 2).size - 1) - 1))

/--
The segment index at position 0 is 1.
-/
@[simp]
theorem segment0 : segment 0 = 1 := by simp [segment]

/--
The segment index at position 1 is 2.
-/
@[simp]
theorem segment1 : segment 1 = 2 := by simp [segment]

/--
Every segment index is positive. Since segments partition the Luby sequence
and indices start from 1, this ensures all segment values are at least 1.
-/
theorem segment_is_pos : ∀ n : ℕ, segment n > 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [segment.eq_def]
    split
    · exact Nat.one_pos
    · expose_names
      split <;> expose_names
      · exact Nat.two_pow_pos ((n + 2).size - 2)
      · simp

-- #eval List.range 32 |>.map (fun n ↦ (n, segment n))
/--
The segment index for position `n` is bounded by `n + 1`.
This upper bound comes from the fact that each position belongs to at most
one segment, and segments are numbered sequentially starting from 1.
-/
theorem segment_limit' (n : ℕ) : segment n ≤ n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [segment.eq_def]
    split
    · expose_names ; simp
    · expose_names
      split
      have n_ge_2 : n ≥ 2 := by
        by_cases n_eq_1 : n = 1
        · expose_names
          simp [n_eq_1] at h_1
        · expose_names
          by_cases n_eq_0 : n = 0
          · replace h := h n_eq_0
            contradiction
          · refine (two_le_iff n).mpr ?_
            · constructor
              · exact h
              · exact n_eq_1
      have n2size_ge_3 : (n + 2).size ≥ 3 := by
        have s1 : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right n_ge_2 2
        replace s1 : (n + 2).size ≥ (2 + 2).size := by exact size_le_size s1
        have s2 : (2 + 2).size = 3 := by simp [size, binaryRec]
        simp [s2] at s1
        exact s1
      · expose_names
        replace h_1 : n + 1 = 2 ^ ((n + 2).size - 1) - 1 := by
          have : n + 1 = 2 ^ ((n + 2).size - 1) - 2 + 1 := congrFun (congrArg HAdd.hAdd h_1) 1
          rw [this]
          grind
        simp [h_1]
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
        by_cases n_eq_1_or_3 : n = 1 ∨ n = 3
        · rcases n_eq_1_or_3 with n_def|n_def
          <;> simp [n_def, size, binaryRec]
        · have n_ge_4 : n ≥ 4 := by
            by_contra n_le_3
            simp at n_le_3
            push_neg at n_eq_1_or_3
            by_cases n_0 : n = 0
            · replace h := h n_0 ; contradiction
            · replace h : n ≥ 1 := by exact one_le_iff_ne_zero.mpr h
              replace h : n = 1 ∨ n > 1 := by exact LE.le.eq_or_lt' h
              rcases h with h_1|h
              · exact absurd h_1 n_eq_1_or_3.left
              · replace h : n ≥ 2 := by exact h
                replace h : n = 2 ∨ n > 2 := by exact LE.le.eq_or_lt' h
                rcases h with h_2|h
                · simp [h_2, size, binaryRec] at h_1
                · replace h : n ≥ 3 := by exact h
                  replace h : n = 3 ∨ n > 3 := by exact LE.le.eq_or_lt' h
                  rcases h with h_3|h
                  · exact absurd h_3 n_eq_1_or_3.right
                  · replace h : ¬n < 4 := by exact Nat.not_lt.mpr h
                    exact absurd n_le_3 h
          have nsize_ge_3 : n.size ≥ 3 := by
            have s1 : n.size ≥ (4 : ℕ).size := size_le_size n_ge_4
            rw (occs := .pos [2]) [size] at s1
            simp [binaryRec] at s1
            exact s1
          have n2size_ge_3 : (n + 2).size ≥ 3 := by
            have s1 : n + 2 ≥ 4 + 2 := Nat.add_le_add n_ge_4 AtLeastTwo.prop
            replace s1 : (n + 2).size ≥ (4 + 2).size := size_le_size s1
            have : (4 + 2).size = 3 := by simp [size, binaryRec]
            simp [this] at s1
            exact s1
          by_cases n1_is_pow2 : n + 1 = 2 ^ n.size
          · have n1size_eq_nsize_add_1 : (n + 1).size = n.size + 1 := by
              exact increase_n1size_iff_pow2.mpr n1_is_pow2
            have n2size_eq_nsize_add_1 : (n + 2).size = n.size + 1 := by
              exact increase_n2size_if_pow2₁ n_ge_4 n1_is_pow2
            simp [n2size_eq_nsize_add_1]
            replace n1_is_pow2 : n = 2 ^ n.size - 1 := Nat.eq_sub_of_add_eq n1_is_pow2
            simp [←n1_is_pow2]
            exact n_lower (zero_lt_of_ne_zero h)
          · rename' n1_is_pow2 => n1_ne_pow2
            by_cases n2_is_pow2 : n + 2 = 2 ^ n.size
            · have n2size_eq_nsize_add_1 : (n + 2).size = n.size + 1 := increase_n2size_if_pow2₂ n n2_is_pow2
              have n1size_eq_nsize : (n + 1).size = n.size := same_n1size_iff_not_pow2.mp n1_ne_pow2
              simp [n2size_eq_nsize_add_1, ←n2_is_pow2]
              exact n_lower (zero_lt_of_ne_zero h)
            · rename' n2_is_pow2 => n2_ne_pow2
              have n2size_eq_nsize : (n + 2).size = n.size := by
                refine same_n2size_iff_not_pow2'.mp ?_
                · exact Decidable.not_imp_iff_and_not.mp fun a ↦ n1_ne_pow2 (a n2_ne_pow2)
              have n1size_eq_nsize : (n + 1).size = n.size := same_n1size_iff_not_pow2.mp n1_ne_pow2
              simp [n2size_eq_nsize]
              have arg1 : n - (2 ^ (n.size - 1) - 1) < n := by
                refine sub_lt ?_ ?_
                · exact zero_lt_of_ne_zero h
                · exact zero_lt_sub_of_lt (Nat.one_lt_two_pow (sub_ne_zero_of_lt (lt_of_add_left_lt nsize_ge_3)))
              replace ih := ih (n - (2 ^ (n.size - 1) - 1)) arg1
              have s1 :
                  2 ^ (n.size - 2) + segment (n - (2 ^ (n.size - 1) - 1)) ≤
                  2 ^ (n.size - 2) + (n - (2 ^ (n.size - 1) - 1) + 1) := by
                exact Nat.add_le_add_iff_left.mpr ih
              have s2 : 2 ^ (n.size - 2) + (n - (2 ^ (n.size - 1) - 1) + 1) ≤ n := by
                have : 2 ^ (n.size - 2) + (n - (2 ^ (n.size - 1) - 1) + 1) =
                    2 ^ (n.size - 2) + n - 2 ^ (n.size - 1) + 2 := by
                  refine Nat.eq_add_of_sub_eq ?_ ?_
                  · have : 2 ≤ 2 ^ (n.size - 2) := le_pow (zero_lt_sub_of_lt nsize_ge_3)
                    exact le_add_right_of_le this
                  · have : (n - (2 ^ (n.size - 1) - 1) + 1) - 2 = n - 2 ^ (n.size - 1) := by grind
                    replace : 2 ^ (n.size - 2) + ((n - (2 ^ (n.size - 1) - 1) + 1) - 2) = 2 ^ (n.size - 2) + (n - 2 ^ (n.size - 1)) := by
                      exact congrArg (HAdd.hAdd (2 ^ (n.size - 2))) this
                    have : 2 ^ (n.size - 2) + ((n - (2 ^ (n.size - 1) - 1) + 1) - 2) =
                        2 ^ (n.size - 2) + (n - (2 ^ (n.size - 1) - 1) + 1) - 2 := by
                          refine Eq.symm (Nat.add_sub_assoc ?_ (2 ^ (n.size - 2)))
                          · refine le_add_of_sub_le ?_
                            · simp
                              have : n - (2 ^ (n.size - 1) - 1) = n - 2 ^ (n.size - 1) + 1 := by
                                refine tsub_tsub_assoc ?_ ?_
                                · exact n_lower (zero_lt_of_ne_zero h)
                                · exact Nat.one_le_two_pow
                              simp [this]
                    simp [←this]
                    replace : n - (2 ^ (n.size - 1) - 1) - 1 = n - 2 ^ (n.size - 1) := by grind
                    simp [this]
                    exact Eq.symm (Nat.add_sub_assoc (n_lower (zero_lt_of_ne_zero h)) (2 ^ (n.size - 2)))
                simp [this]
                replace : 2 ^ (n.size - 1) = 2 ^ (n.size - 2) + 2 ^ (n.size - 2) := by
                  rw [←mul_two]
                  simp [←pow_succ]
                  grind
                simp [this]
                have : 2 ^ (n.size - 2) + n - (2 ^ (n.size - 2) + 2 ^ (n.size - 2)) =
                    n - 2 ^ (n.size - 2) := by
                  exact Nat.add_sub_add_left (2 ^ (n.size - 2)) n (2 ^ (n.size - 2))
                simp [this]
                refine add_le_of_le_sub ?_ ?_
                · exact le_of_add_left_le n_ge_4
                · exact Nat.sub_le_sub_left (le_pow (zero_lt_sub_of_lt nsize_ge_3)) n
              replace s2 : 2 ^ (n.size - 2) + (n - (2 ^ (n.size - 1) - 1) + 1) ≤ n + 1 := le_add_right_of_le s2
              exact Nat.le_trans s1 s2

/--
For n ≥ 2, the segment index at position n is at most n.
This is a tighter bound than segment_limit', showing segments are bounded by their position.
-/
theorem segment_limit {n : ℕ} (n_ge_2 : n ≥ 2) : segment n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [segment.eq_def]
    split
    · expose_names ; contradiction
    · expose_names
      split
      have n2size_ge_3 : (n + 2).size ≥ 3 := by
        have s1 : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right n_ge_2 2
        replace s1 : (n + 2).size ≥ (2 + 2).size := by exact size_le_size s1
        have s2 : (2 + 2).size = 3 := by simp [size, binaryRec]
        simp [s2] at s1
        exact s1
      · expose_names
        rw (occs := .pos [2]) [h_1]
        have : 2 ^ ((n + 2).size - 1) = 2 ^ ((n + 2).size - 2) + 2 ^ ((n + 2).size - 2) := by
          have : 2 ^ ((n + 2).size - 1) = 2 * 2 ^ ((n + 2).size - 1 - 1) := by
            refine Eq.symm (mul_pow_sub_one ?_ 2)
            · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)
          simp [this]
          replace : (n + 2).size - 1 - 1 = (n + 2).size - 2 := by exact rfl
          simp [this]
          exact Nat.two_mul (2 ^ ((n + 2).size - 2))
        simp only [this]
        refine Nat.le_sub_of_add_le' ?_
        · refine Nat.add_le_add_iff_right.mpr ?_
          · refine Nat.le_self_pow ?_ 2
            · exact Nat.sub_ne_zero_iff_lt.mpr n2size_ge_3
      · expose_names
        simp
        replace n_ge_2 : n = 2 ∨ n > 2 := by exact LE.le.eq_or_lt' n_ge_2
        rcases n_ge_2 with eq|n_ge_3
        · simp [eq, size, binaryRec] at h_1
        · replace n_ge_3 : n ≥ 3 := by exact n_ge_3
          replace n_ge_3 : n = 3 ∨ n > 3 := by exact LE.le.eq_or_lt' n_ge_3
          rcases n_ge_3 with eq|n_ge_4
          · simp [eq, size, binaryRec]
          · replace n_ge_4 : n ≥ 4 := by exact n_ge_4
            have n2size_eq_n1size : (n + 2).size = (n + 1).size := by
              refine same_n1size_iff_not_pow2.mp ?_
              · replace h_1 : ¬n + 2 = 2 ^ ((n + 2).size - 1) := by
                  by_contra x
                  have : n = 2 ^ ((n + 2).size - 1) - 2 := by exact Nat.eq_sub_of_add_eq x
                  exact absurd this h_1
                by_contra x
                have : n + 1 + 1 = n + 2 := rfl
                simp [this] at x
                simp [x, size_pow] at h_1
            have n2size_ge_3 : (n + 2).size ≥ 3 := by
              have s1 : n + 2 ≥ 4 + 2 := by refine Nat.add_le_add n_ge_4 AtLeastTwo.prop
              replace s1 : (n + 2).size ≥ (4 + 2).size := by exact size_le_size s1
              have : (4 + 2).size = 3 := by simp [size, binaryRec]
              simp [this] at s1
              exact s1
            by_cases with_carry : n = 2 ^ ((n + 2).size - 1) - 1
            · have n2size_eq_nsize_add_1 : (n + 2).size = n.size + 1 := by
                have s1 : (n + 1).size = n.size + 1 := by
                  simp [n2size_eq_n1size] at with_carry
                  replace with_carry : n.size = (2 ^ ((n + 1).size - 1) - 1).size := by
                    exact congrArg size with_carry
                  have : (2 ^ ((n + 1).size - 1) - 1).size = (n + 1).size - 1 := by
                    refine size_sub ?_ ?_ ?_
                    · refine zero_lt_sub_of_lt ?_
                      · simp [←n2size_eq_n1size] ; exact lt_of_add_left_lt n2size_ge_3
                    · exact Nat.one_pos
                    · exact Nat.one_le_two_pow
                  simp [this] at with_carry
                  simp [with_carry]
                  refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
                  · simp [←n2size_eq_n1size] ; exact lt_of_add_left_lt n2size_ge_3
                simp [←n2size_eq_n1size] at s1
                exact s1
              simp [n2size_eq_nsize_add_1] at *
              have s1 : segment (n - (2 ^ n.size - 1)) = 1 := by
                have t1 : n - (2 ^ n.size - 1) = 0 := by
                  rewrite (occs := .pos [1]) [with_carry]
                  have : 2 ^ n.size = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
                    exact Eq.symm (Nat.two_pow_pred_add_two_pow_pred (zero_lt_of_lt n2size_ge_3))
                  simp [this]
                simp [t1]
              simp [s1]
              rw (occs := .pos [2]) [with_carry]
              have : 2 ^ n.size = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
                rw [←mul_two]
                rw [←pow_succ]
                simp
                grind
              simp [this]
              refine (Nat.le_sub_one_iff_lt ?_).mpr ?_
              · exact pos_of_neZero (2 ^ (n.size - 1) + 2 ^ (n.size - 1))
              · refine Nat.add_lt_add_left ?_ (2 ^ (n.size - 1))
                · exact Nat.one_lt_two_pow (Nat.sub_ne_zero_iff_lt.mpr n2size_ge_3)
            · have n2size_eq_n1size : (n + 2).size = (n + 1).size := by
                by_contra n1size_ne_n2size
                have : (n + 2).size = (n + 1).size + 1 := by
                  have : (n + 2).size = (n + 1).size ∨ (n + 2).size = (n + 1).size + 1 := by
                    exact size_limit (n + 1)
                  rcases this with c|c
                  · exact absurd c n1size_ne_n2size
                  · exact c
                have : n + 2 = 2 ^ ((n + 2).size - 1) := by
                  exact False.elim (n1size_ne_n2size n2size_eq_n1size)
                replace : n = 2 ^ ((n + 2).size - 1) - 2 := Nat.eq_sub_of_add_eq this
                exact absurd this h_1
              have n2size_eq_nsize : (n + 2).size = n.size := by
                have s2 : n.size = (n + 1).size := by
                  by_contra nsize_ne_n1size
                  have : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := size_limit n
                  rcases this with c|c
                  · simp [c] at nsize_ne_n1size
                  · have : n + 1 = 2 ^ ((n + 1).size - 1) := by
                      simp [c]
                      exact increase_n1size_iff_pow2.mp c
                    replace : n = 2 ^ ((n + 1).size - 1) - 1 := Nat.eq_sub_of_add_eq this
                    simp [←n2size_eq_n1size] at this
                    exact absurd this with_carry
                simp [←n2size_eq_n1size] at s2
                exact id (Eq.symm s2)
              have ih1 : n - (2 ^ ((n + 2).size - 1) - 1) < n := by
                refine sub_lt ?_ ?_
                · exact zero_lt_of_ne_zero h
                · refine zero_lt_sub_of_lt ?_
                  · refine Nat.one_lt_two_pow_iff.mpr ?_
                    · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)
              have ih2 : n + 2 ≥ 2 ^ ((n + 2).size - 1) := by
                have : n + 2 ≥ 2 ^ ((n + 2).size - 1) := by
                  exact n_ge_subenvelope (Nat.le_add_left 1 (n + 1))
                exact this
              have ih2' : n ≥ 2 ^ ((n + 2).size - 2) := by
                have : 2 ^ ((n + 2).size - 1) > 2 ^ ((n + 2).size - 2) := by
                  refine (Nat.pow_lt_pow_iff_right ?_).mpr ?_
                  · exact Nat.one_lt_two
                  · exact sub_succ_lt_self (n + 2).size 1 (lt_of_add_left_lt n2size_ge_3)
                grind
              simp [n2size_eq_nsize]
              by_cases n_range : n - (2 ^ (n.size - 1) - 1) = 0
              · simp [n_range]
                have s1 : 1 ≤ 2 ^ (n.size - 2) := by exact Nat.one_le_two_pow
                have s2 : 2 ^ (n.size - 1) ≤ n := by exact n_ge_subenvelope (one_le_of_lt n_ge_4)
                replace s2 : 2 ^ (n.size - 2) + 2 ^ (n.size - 2) ≤ n := by
                  have : 2 ^ (n.size - 2) + 2 ^ (n.size - 2) = 2 ^ (n.size - 1) := by
                    have : 2 ^ (n.size - 2) + 2 ^ (n.size - 2) = 2 ^ (n.size - 2 + 1) := by
                      exact Eq.symm (two_pow_succ (n.size - 2))
                    simp [this]
                    grind
                  simp [this]
                  exact s2
                exact add_le_of_add_le_left s2 s1
              · simp [n2size_eq_nsize] at *
                by_cases n_is_pow2 : n = 2 ^ (n.size - 1)
                · simp [←n_is_pow2] at *
                  have : n - (n - 1) = 1 := by
                    refine Nat.sub_sub_self ?_
                    · exact one_le_of_lt n_ge_4
                  simp [this]
                  have s1 : 2 ^ (n.size - 2) + 2 ^ (n.size - 2) ≤ n := by
                    have t1 : 2 ^ (n.size - 1) ≤ n := by
                      refine n_ge_subenvelope ?_
                      · exact one_le_of_lt n_ge_4
                    have t2 : 2 ^ (n.size - 1) = 2 ^ (n.size - 2) + 2 ^ (n.size - 2) := by
                      have : 2 ^ (n.size - 1) = 2 * 2 ^ ((n.size - 1) - 1) := by
                        refine Eq.symm (mul_pow_sub_one ?_ 2)
                        · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)
                      simp [this]
                      replace : (n.size - 1) - 1 = n.size - 2 := by exact rfl
                      simp [this]
                      exact Nat.two_mul (2 ^ (n.size - 2))
                    simp [t2] at t1
                    exact t1
                  have s2 : 2 ≤ 2 ^ (n.size - 2) := by
                    exact le_pow (zero_lt_sub_of_lt n2size_ge_3)
                  exact add_le_of_add_le_left s1 s2
                · replace n'_eq_0 : n - (2 ^ (n.size - 1) - 1) > 0 := by
                    exact zero_lt_of_ne_zero n_range
                  have cond1 : n - (2 ^ (n.size - 1) - 1) < n := by
                    refine sub_lt ?_ ?_
                    · exact zero_lt_of_ne_zero h
                    · refine zero_lt_sub_of_lt ?_
                      · refine Nat.one_lt_two_pow ?_
                        · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)
                  have cond2 : n - (2 ^ (n.size - 1) - 1) ≥ 2 := by
                    have : n ≥ 2 + (2 ^ (n.size - 1) - 1) := by
                      have : n ≥ 2 + 2 ^ (n.size - 1) - 1 := by
                        have : n ≥ 2 ^ (n.size - 1) + 2 - 1 := by
                          have : n ≥ 2 ^ (n.size - 1) + 1 := by
                            have s1 : n ≥ 2 ^ (n.size - 1) := by
                              exact n_ge_subenvelope (one_le_of_lt n_ge_4)
                            have d2 : ¬n = 2 ^ (n.size - 1) := by
                              by_contra n_eq_pow2
                              simp [←n_eq_pow2] at *
                            have : n > 2 ^ (n.size - 1) := by
                              exact Nat.lt_of_le_of_ne s1 fun a ↦ d2 (id (Eq.symm a))
                            exact this
                          exact this
                        grind
                      grind
                    grind
                  have ih' := ih (n - (2 ^ (n.size - 1) - 1)) cond1 cond2
                  have : 2 ^ (n.size - 2) + (n - (2 ^ (n.size - 1) - 1)) ≤ n := by
                    have t1 : 2 ^ (n.size - 1) = 2 ^ (n.size - 2) + 2 ^ (n.size - 2) := by
                      have : 2 ^ (n.size - 1) = 2 * 2 ^ ((n.size - 1) - 1) := by
                        refine Eq.symm (mul_pow_sub_one ?_ 2)
                        · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt n2size_ge_3)
                      simp [this]
                      replace : (n.size - 1) - 1 = n.size - 2 := by exact rfl
                      simp [this]
                      exact Nat.two_mul (2 ^ (n.size - 2))
                    simp [t1]
                    refine (Nat.le_sub_iff_add_le' ih2').mp ?_
                    · refine Nat.sub_le_sub_left ?_ n
                      · refine le_sub_one_of_lt ?_
                        · refine Nat.lt_add_of_pos_right ?_
                          · exact Nat.two_pow_pos (n.size - 2)
                  exact add_le_of_add_le_left this (ih (n - (2 ^ (n.size - 1) - 1)) cond1 cond2)

-- #eval List.range 64 |>.map (fun n ↦ (n, segment n, 2 ^ ((n + 1).size - 1)))
/--
For n ≥ 2, the segment index is bounded by 2^((n+1).size - 1).
This provides a logarithmic upper bound on segment indices.
-/
theorem segment_limit2 {n : ℕ} (n_ge : n ≥ 2) : segment n ≤ 2 ^ ((n + 1).size - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have nsize_le_self : 2 ^ (n.size - 1) ≤ n := n_lower (zero_lt_of_lt n_ge)
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
              · have n1size_eq_nsize_add_1 : (n + 1).size = n.size + 1 := by
                  exact increase_n1size_iff_pow2.mpr n1_is_pow2
                have n2size_eq_n1size : (n + 2).size = (n + 1).size := by
                  have : n + 1 + 1 = 2 ^ n.size + 1 := congrFun (congrArg HAdd.hAdd n1_is_pow2) 1
                  replace : n + 2 = 2 ^ n.size + 1 := this
                  replace : (n + 2).size = (2 ^ n.size + 1).size := congrArg size this
                  replace : (n + 2).size = n.size + 1 := increase_n2size_if_pow2₁ n_ge_4 n1_is_pow2
                  simp [←n1size_eq_nsize_add_1] at this
                  exact this
                simp [n1size_eq_nsize_add_1, n2size_eq_n1size] at *
                exact Luby.pow2_le_pow2 (n.size - 1) n.size (sub_le n.size 1)
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
                exact (Nat.sub_eq_iff_eq_add (one_le_of_lt n2size_ge_3)).mp n1size_eq_nsize
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
                  have n1size_eq_nsize : (n + 1).size = n.size := same_n1size_iff_not_pow2.mp n1_ne_pow2
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
                  have arg1 : (n - (2 ^ (n.size - 1) - 1)) < n := by
                    refine sub_lt ?_ ?_
                    · exact zero_lt_of_ne_zero h
                    · refine zero_lt_sub_of_lt ?_
                      · refine Nat.one_lt_two_pow ?_
                        · exact Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt nsize_ge_3)
                  have arg2 : 2 ≤ (n - (2 ^ (n.size - 1) - 1)) := by
                    have s1 : 2 ^ (n.size - 1) ≤ n := nsize_le_self
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
                    · clear this ih arg1 arg2 h n1size_eq_nsize n2size_eq_nsize n1size_ge_3 n2size_ge_3
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
                        have : n - (2 ^ (n.size - 1) - 1) + 1 < 2 ^ (n.size - 1) := by
                          replace : n < 2 ^ n.size := by exact lt_size_self n
                          replace : n - 2 ^ (n.size - 1) < 2 ^ n.size - 2 ^ (n.size - 1) := by
                            exact Nat.sub_lt_sub_right nsize_le_self this
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
                              · exact le_add_right_of_le nsize_le_self
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
                          replace :
                              n - 2 ^ (n.size - 1) + 1 = 2 ^ (n.size - 1) ∨
                              n - 2 ^ (n.size - 1) + 1 < 2 ^ (n.size - 1) := by
                            exact Nat.eq_or_lt_of_le this
                          rcases this with eq|gt
                          · exact absurd eq aux
                          · replace gt : n - 2 ^ (n.size - 1) + 1 + 1 ≤ 2 ^ (n.size - 1) := gt
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
                                  exact Eq.symm (Nat.sub_add_comm nsize_le_self)
                                simp [left] at eq
                                replace eq : n + 2 = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
                                  refine (Nat.sub_eq_iff_eq_add ?_).mp eq
                                  · exact le_add_right_of_le nsize_le_self
                                simp [←pow2_nsize_divide] at eq
                                exact eq
                              exact absurd this n2_ne_pow2
                            · replace aux : n - (2 ^ (n.size - 1) - 1) = n - 2 ^ (n.size - 1) + 1 := by
                                exact tsub_tsub_assoc nsize_le_self Nat.one_le_two_pow
                              simp [aux]
                              exact gt
                        replace : (n - (2 ^ (n.size - 1) - 1) + 1).size ≤ n.size - 1 := size_le.mpr this
                        replace : (n - (2 ^ (n.size - 1) - 1) + 1).size < n.size - 1 + 1 := by
                          exact Order.lt_add_one_iff.mpr this
                        have it : n.size - 1 + 1 = n.size := by grind
                        simp [it] at this
                        exact this
                      replace s1 : (n - (2 ^ (n.size - 1) - 1) + 1).size ≤ n.size - 1 := le_sub_one_of_lt s1
                      replace s1 : (n - (2 ^ (n.size - 1) - 1) + 1).size - 1 ≤ n.size - 1 - 1 := by
                        exact Nat.sub_le_sub_right s1 1
                      exact Luby.pow2_le_pow2 ((n - (2 ^ (n.size - 1) - 1) + 1).size - 1) (n.size - 2) s1
                  exact add_le_of_add_le_left s1 ih

/--
The segment function is monotone: `segment n ≤ segment (n + 1)` for all `n`.
Segments form a non-decreasing sequence as positions increase through the Luby sequence.
-/
theorem segment_is_monotone : ∀ n : ℕ, segment n ≤ segment (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [segment.eq_def]
    split
    · expose_names ; simp
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
          refine size_of_pow2 ?_
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
            have n_ge_1 : n ≥ 1 := by exact one_le_iff_ne_zero.mpr h
            have n2size_ge_2 : (n + 2).size ≥ 2 := by exact size0_add_2_ge_2 n
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
            have s1 : segment (2 ^ ((n + 2).size - 1) - 2) = 2 ^ ((n + 2).size - 2) := by
              rw [segment.eq_def]
              split
              · expose_names
                replace heq : 2 ^ ((n + 2).size - 1) - 2 + 2 = 0 + 2 := by
                  exact congrFun (congrArg HAdd.hAdd heq) 2
                have : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
                  refine Nat.sub_add_cancel ?_
                  · refine le_pow ?_
                    · exact zero_lt_sub_of_lt n2size_ge_2
                simp [this] at heq
                replace : 2 ^ ((n + 2).size - 1) = 2 * 2 ^ ((n + 2).size - 1 - 1) := by
                  exact Eq.symm (mul_pow_sub_one (Nat.sub_ne_zero_iff_lt.mpr n2size_ge_2) 2)
                simp only [this] at heq
                replace : 2 = 2 * 1 := rfl
                rewrite (occs := .pos [4]) [this] at heq
                have (a b c : ℕ) (h : a > 0) : a * b = a * c → b = c := by
                  exact fun a_1 ↦ Nat.eq_of_mul_eq_mul_left h a_1
                have two_gt_0 : 0 < 2 := by exact Nat.zero_lt_two
                have goal := Nat.eq_of_mul_eq_mul_left two_gt_0 heq
                replace : (n + 2).size - 1 - 1 = (n + 2).size - 2 := by
                  exact
                    this n ((n + 2).size - 1 - 1) ((n + 2).size - 2) n_ge_1
                      (this n (n * ((n + 2).size - 1 - 1)) (n * ((n + 2).size - 2)) n_ge_1 rfl)
                simp only [this] at goal
                exact id (Eq.symm goal)
              · expose_names
                have s1 : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
                  exact Nat.sub_add_cancel (Nat.le_self_pow (Nat.sub_ne_zero_iff_lt.mpr n2size_ge_2) 2)
                have s2 : (2 ^ ((n + 2).size - 1)).size = (n + 2).size - 1 + 1 := size_pow
                split
                · simp [s1, s2]
                  replace : (n + 2).size - 1 - 1 = (n + 2).size - 2 := rfl
                  simp [this]
                · expose_names
                  simp [s1, s2] at h_5
            · simp [s1, n3size_eq_n2size]
              have : (n + 2).size - 1 - 1 = (n + 2).size - 2 := rfl
              simp [←this]
              replace : 0 < (n + 2).size - 1 := by exact zero_lt_sub_of_lt n2size_ge_2
              rw [Nat.two_pow_pred_add_two_pow_pred this]
          · expose_names
            simp
            replace h_1 : ¬n + 2 = 2 ^ ((n + 2).size - 1) := by
              by_contra case_if
              replace case_if : n = 2 ^ ((n + 2).size - 1) - 2 := by grind
              simp [←case_if] at h_1
            replace h_3 : ¬n + 2 + 1 = 2 ^ ((n + 2 + 1).size - 1) := by
              have ordering : n + 1 + 2 = n + 2 + 1 := by exact rfl
              simp [ordering] at *
              by_contra case_if
              replace case_if : n + 1 = 2 ^ ((n + 2 + 1).size - 1) - 2 := by grind
              simp [case_if] at h_3
            have n3size_eq_n2size : (n + 2 + 1).size = (n + 2).size := by
              have ordering : n + 1 + 2 = n + 2 + 1 := by exact rfl
              simp [ordering] at *
              refine same_n1size_iff_not_pow2.mp ?_
              · by_contra x
                have : (n + 2 + 1).size = (n + 2).size + 1 := increase_n1size_iff_pow2.mpr x
                simp [this, ←x] at h_3
            simp [n3size_eq_n2size]
            have : n + 1 - (2 ^ ((n + 2).size - 1) - 1) = n - (2 ^ ((n + 2).size - 1) - 1) + 1 := by
              refine Nat.sub_add_comm ?_
              · have : 2 ^ ((n + 2).size - 1) ≤ n + 2 := n_ge_subenvelope (Nat.le_add_left 1 (n + 1))
                replace : 2 ^ ((n + 2).size - 1) < n + 2 := by
                  exact Nat.lt_of_le_of_ne this fun a ↦ h_1 (id (Eq.symm a))
                replace : 2 ^ ((n + 2).size - 1) ≤ n + 1 := by exact le_of_lt_succ this
                exact sub_le_of_le_add this
            simp [this]
            have s1 : n - (2 ^ ((n + 2).size - 1) - 1) < n := by
              refine sub_lt ?_ ?_
              · exact zero_lt_of_ne_zero h
              · refine zero_lt_sub_of_lt ?_
                · have s1 : n ≥ 1 := by exact one_le_iff_ne_zero.mpr h
                  replace s1 : (n + 2).size ≥ (1 + 2).size := by
                    exact size_le_size (Nat.add_le_add_right s1 2)
                  have s2 : (1 + 2).size = 2 := by simp [size, binaryRec]
                  simp only [s2] at s1
                  exact Nat.one_lt_two_pow (Nat.sub_ne_zero_iff_lt.mpr s1)
            exact ih (n - (2 ^ ((n + 2).size - 1) - 1)) s1

/--
Monotonicity over arbitrary intervals: if a ≤ b, then segment a ≤ segment b.
This generalizes segment_is_monotone to non-adjacent positions.
-/
theorem segment_is_monotone' {a b : ℕ} (h : a ≤ b) : segment a ≤ segment b := by
  let d := b - a
  have d_def : d = value_of% d := by exact rfl
  have d_as_b : b = a + d := by exact Eq.symm (add_sub_of_le h)
  simp [d_as_b]
  induction d with
  | zero => simp
  | succ d ih =>
    have : a + (d + 1) = a + d + 1 := by exact rfl
    simp [this]
    replace : segment (a + d) ≤ segment (a + d + 1) := by exact segment_is_monotone (a + d)
    exact Nat.le_trans ih this

-- #eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n))
-- #eval! List.range 8 |>.map (2 ^ ·.succ - 2) |>.map (fun n ↦ (n, LubySegment.segment n))
/- #eval! List.range 8
  |>.map (2 ^ ·.succ - 2)
  |>.map (fun n ↦
    ( n,
      2 ^ (n.size + 1) - 2,
      LubySegment.segment n,
      segment (2 ^ (n + 2).size - 2))) -/

/--
At envelope boundaries (where `n = 2 ^ n.size - 2`), the segment index doubles
when jumping to the next envelope. This reflects the tree structure of the Luby sequence,
where each new level contains twice as many segments as the previous level.
-/
theorem segment_prop1' : ∀ n : ℕ, n = 2 ^ n.size - 2 →
    segment (2 ^ (n + 2).size - 2) = 2 * segment n := by
  intro n  envelope
  by_cases n_gt_0 : n = 0
  · simp [n_gt_0, size, binaryRec, segment]
  · replace n_gt_0 : n > 0 := by exact zero_lt_of_ne_zero n_gt_0
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
At envelope boundaries (where `n = 2 ^ n.size - 2`), the segment index equals `2 ^ (n.size - 1)`.
This provides a direct formula for segment values at envelope positions.
-/
theorem segment_prop1 {n : ℕ} (h' : n = 2 ^ n.size - 2) : segment n = 2 ^ (n.size - 1) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases n_eq_0 : n = 0
      · simp [n_eq_0]
      · have n_ge_2 : n ≥ 2 := by
          replace n_eq_0 : n ≥ 1 := by exact one_le_iff_ne_zero.mpr n_eq_0
          replace n_eq_0 : n = 1 ∨ n > 1 := by exact LE.le.eq_or_lt' n_eq_0
          rcases n_eq_0 with eq|gt
          · simp [eq] at h'
          · exact gt
        by_cases n_eq_2 : n = 2
        · simp [n_eq_2, segment, size, binaryRec]
        · have n_ge_4 : n ≥ 4 := by
            have : n > 2 := by exact Nat.lt_of_le_of_ne n_ge_2 fun a ↦ n_eq_2 (id (Eq.symm a))
            replace : n ≥ 3 := by exact this
            by_cases n_eq_3 : n = 3
            · simp [n_eq_3] at h'
            · replace : n = 3 ∨ n > 3 := by exact LE.le.eq_or_lt' this
              rcases this with c|c
              · exact absurd c n_eq_3
              · exact c
          have nsize_ge_3 : n.size ≥ 3 := size4_add_0_ge_2 n_ge_4
          have n2size_ge_3 : (n + 2).size ≥ 3 := size2_add_2_ge_2 n_ge_2
          rw [segment]
          simp
          split
          · expose_names
            have : (n + 2).size = n.size + 1 := by
              replace h : n + 2 = 2 ^ ((n + 2).size - 1) := by
                have s1 : n + 2 = 2 ^ ((n + 2).size - 1) - 2 + 2 := by
                  exact congrFun (congrArg HAdd.hAdd h) 2
                have s2 : 2 ^ ((n + 2).size - 1) - 2 + 2 = 2 ^ ((n + 2).size - 1) := by
                  refine Nat.sub_add_cancel ?_
                  · refine le_pow ?_
                    · refine zero_lt_sub_of_lt ?_
                      · have t1 : n + 2 ≥ 4 + 2 := by exact Nat.add_le_add_right n_ge_4 2
                        replace t1 : (n + 2).size ≥ (4 + 2).size := by exact size_le_size t1
                        have t2 : (4 + 2).size = 3 := by simp [size, binaryRec]
                        simp [t2] at t1
                        exact lt_of_add_left_lt t1
                simp [s2] at s1
                exact s1
              have : (n + 2).size = n.size + 1 := by
                have s1 : n + 2 - 1 = 2 ^ ((n + 2).size - 1) - 1 := congrFun (congrArg HSub.hSub h) 1
                replace s1 : (n + 2 - 1).size = (2 ^ ((n + 2).size - 1) - 1).size := congrArg size s1
                have s2 : (2 ^ ((n + 2).size - 1) - 1).size = (n + 2).size - 1 := by
                  refine size_sub ?_ ?_ ?_
                  · exact zero_lt_sub_of_lt (lt_of_add_left_lt n2size_ge_3)
                  · exact Nat.one_pos
                  · exact Nat.one_le_two_pow
                simp [s2] at s1
                replace h : n + 2 - 2 = 2 ^ ((n + 2).size - 1) - 2 := congrFun (congrArg HSub.hSub h) 2
                replace h : (n + 2 - 2).size = (2 ^ ((n + 2).size - 1) - 2).size := congrArg size h
                replace h : n.size = (n + 2).size - 1 := by
                  have : n + 2 - 2 = n := rfl
                  simp [this] at h
                  replace : (2 ^ ((n + 2).size - 1) - 2).size = (n + 2).size - 1 := by
                    refine size_sub ?_ ?_ ?_
                    · exact zero_lt_sub_of_lt (lt_of_add_left_lt n2size_ge_3)
                    · exact Nat.zero_lt_two
                    · exact le_pow (zero_lt_sub_of_lt (lt_sub_of_add_lt n2size_ge_3))
                  simp [this] at h
                  exact h
                exact Nat.eq_add_of_sub_eq (one_le_of_lt n2size_ge_3) (id (Eq.symm h))
              exact this
            simp [this]
          · expose_names
            have h'' : n + 2 = 2 ^ n.size := by
              refine Eq.symm (Nat.eq_add_of_sub_eq ?_ (id (Eq.symm h')))
              · exact le_pow (size_pos.mpr (zero_lt_of_ne_zero n_eq_0))
            simp [h'', size_pow] at h
            exact absurd h' h
          · intro z
            exact absurd z n_eq_0

/--
For positions not at envelope boundaries, the segment index is computed recursively:
`segment n = 2 ^ ((n + 2).size - 2) + segment (n - (2 ^ ((n + 2).size - 1) - 1))`.
This formula reflects the recursive structure of the Luby sequence, where non-envelope
positions reference earlier positions in the sequence.
-/
theorem segment_prop2 : ∀ n > 0, ¬n = 2 ^ n.size - 2 →
    segment n = 2 ^ ((n + 2).size - 2) + segment (n - (2 ^ ((n + 2).size - 1) - 1)) := by
  intro n n_gt_0 n_ne_envelope
  have n2size : (n + 2).size ≥ 2 := by
    have s1 : (n + 2).size ≥ (0 + 2).size := by
      exact size_le_size (Nat.le_add_left (0 + 2) n)
    exact size0_add_2_ge_2 n
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

/--
Return the length of segment of state `n`.
So `n` starts from zero. -/
def segment_length (n : ℕ) : ℕ := trailing_zeros (segment n) + 1
-- #eval! List.range 32 |>.map (fun n ↦ (n, LubySegment.segment n, LubySegment.segment_length n))
-- example : segment_length 0 = 1 := by simp [segment_length]

@[simp]
theorem segment_length_of_0_eq_1 : segment_length 0 = 1 := by simp [segment_length]

@[simp]
theorem segment_length_of_1_eq_2 : segment_length 1 = 2 := by simp [segment_length]

@[simp]
theorem segment_length_of_2_eq_2 : segment_length 2 = 2 := by simp [segment_length, segment]

#eval List.range 64
  |>.filter (fun n ↦ n = 2 ^ n.size - 2)
  |>.map (fun n ↦ (n, 1 + segment_length (n - 2 ^ ((n + 2).size - 2)) , segment_length n))

/--
At envelope boundaries, the segment length increases by 1 when moving backwards by `2 ^ ((n + 2).size - 2)`.
This recursive relationship characterizes how segment lengths evolve at envelope positions.
-/
theorem segment_length_prop1 : ∀ n > 0, n = 2 ^ n.size - 2 →
    segment_length n = segment_length (n - 2 ^ ((n + 2).size - 2)) + 1 := by
  intro n n_gt_0 n_is_envelope
  have n_gt_2 : n ≥ 2 := by
    by_contra n_eq_1
    simp at n_eq_1
    have : n = 1 := by exact Nat.eq_of_le_of_lt_succ n_gt_0 n_eq_1
    simp [this] at n_is_envelope
  by_cases n_eq_2 : n = 2
  · simp [n_eq_2, segment_length, segment, size, binaryRec]
  · have n_ge_4 : n ≥ 4 := by
      have n_ge_3 : n > 2 := by
        exact Nat.lt_of_le_of_ne n_gt_2 fun a ↦ n_eq_2 (id (Eq.symm a))
      replace n_ge_3 : n ≥ 3 := by exact n_ge_3
      have : ¬n = 3 := by
        by_contra n_eq_3
        simp [n_eq_3] at n_is_envelope
      replace : n > 3 := by exact Nat.lt_of_le_of_ne n_ge_3 fun a ↦ this (id (Eq.symm a))
      exact this
    have nsize_ge_: n.size ≥ 3 := by exact size4_add_0_ge_2 n_ge_4
    have n2size_eq_nsize1 : (n + 2).size = n.size + 1 := by
      have : n + 2 = 2 ^ n.size := by
        refine
          Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add h).mp) ?_ (id (Eq.symm n_is_envelope)))
        · refine le_pow ?_
          · exact size_pos.mpr n_gt_0
      simp [this, size_pow]
    simp [n2size_eq_nsize1] at *
    simp [segment_length]
    have : n - 2 ^ (n.size - 1) = 2 ^ (n.size - 1) - 2 := by
      rewrite (occs := .pos [1]) [n_is_envelope]
      have : 2 ^ n.size = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) := by
        have : n.size = n.size - 1 + 1 := by
          refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
          · exact one_le_of_lt nsize_ge_
        rw (occs := .pos [1]) [this]
        rw[Nat.pow_succ', mul_comm, mul_two]
      simp [this]
      grind
    simp [this]
    have segment_of_n : segment n = 2 ^ (n.size - 1) := by
      rw [segment]
      split
      · expose_names
        rw (occs := .pos [1]) [n_is_envelope]
        replace : 2 ^ n.size - 2 + 2 = 2 ^ n.size := by
          refine Nat.sub_add_cancel ?_
          · refine le_pow ?_
            · exact size_pos.mpr n_gt_0
        simp [this]
        rw [size_pow]
        grind
      · expose_names
        have n_is_envelope' : n + 2 = 2 ^ n.size := by
          refine Eq.symm (Nat.eq_add_of_sub_eq ?_ (id (Eq.symm n_is_envelope)))
          · refine le_pow ?_
            · exact size_pos.mpr n_gt_0
        simp [n_is_envelope'] at h
        rw [size_pow] at h
        simp at h
        exact absurd n_is_envelope h
      · intro n_eq_0
        have : ¬n = 0 := by exact Nat.ne_zero_of_lt n_gt_0
        exact absurd n_eq_0 this
    simp [segment_of_n]
    simp [trailing_zeros_prop3 (n.size - 1)]
    have segment_value : segment (2 ^ (n.size - 1) - 2) = 2 ^ (n.size - 1 - 1) := by
      let x := 2 ^ (n.size - 1) - 2
      have x_def : x = value_of% x := by exact rfl
      have x_is_envelope : x = 2 ^ x.size - 2 := by
        simp [x_def]
        have : (2 ^ (n.size - 1) - 2).size = n.size - 1 := by
          refine size_sub ?_ ?_ ?_
          · refine zero_lt_sub_of_lt ?_
            · exact lt_size.mpr n_gt_2
          · exact Nat.zero_lt_two
          · refine le_pow ?_
            · refine zero_lt_sub_of_lt ?_
              · exact lt_sub_of_add_lt nsize_ge_
        simp [this]
      have : segment x = 2 ^ (x.size - 1) := by exact segment_prop1 x_is_envelope
      simp [x_def] at this
      simp [this]
      replace : (2 ^ (n.size - 1) - 2).size = n.size - 1 := by
        refine size_sub ?_ ?_ ?_
        · refine zero_lt_sub_of_lt ?_
          · exact lt_size.mpr n_gt_2
        · exact Nat.zero_lt_two
        · refine le_pow ?_
          · refine zero_lt_sub_of_lt ?_
            · exact lt_sub_of_add_lt nsize_ge_
      simp [this]
    simp [segment_value]
    rw [trailing_zeros_prop3 (n.size - 1 - 1)]
    grind

#eval List.range 64
  |>.filter (fun n ↦ n = 2 ^ n.size - 2)
  |>.map (fun n ↦ (n, segment_length (2 ^ (n + 2).size - 2) , 1 + segment_length n))

/--
At envelope boundaries (where `n = 2 ^ n.size - 2`), the segment length increases by 1
when jumping to the next envelope: `segment_length (2 ^ (n + 2).size - 2) = 1 + segment_length n`.
This reflects the fact that each new envelope level in the Luby tree adds one more element
to the maximum segment height.
-/
theorem segment_length_prop1_ : ∀ n > 0, n = 2 ^ n.size - 2 →
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
        simp at s1
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

#eval List.range 62
  |>.filter (fun n ↦ ¬segment n = 2 ^ ((n + 1).size - 1))
  |>.map (fun n ↦ (n, segment_length (n - (2 ^ ((n + 1).size - 1) - 1)), segment_length n))

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
      have s2 : (3 + 2).size = 3 := by simp [size, binaryRec]
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
        · simp [eq, size, binaryRec] at n_is_envelope'
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
                · refine Nat.ne_zero_iff_zero_lt.mpr ?_
                  · exact size_pos.mpr n_gt_0
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
          simp [size, binaryRec, trailing_zeros]
        · replace n_ge_4 : n ≥ 4 := by exact n_ge_4
          have n_ge_7 : n ≥ 7 := by -- envelope segmentではないので言えるはず
            have n_lower : n = 4 ∨ n > 4 := by exact LE.le.eq_or_lt' n_ge_4
            rcases n_lower with eq|gt
            · simp [eq, segment, size, binaryRec] at n_ne_envelope_segment
            · replace gt : n ≥ 5 := by exact gt
              replace n_lower : n = 5 ∨ n > 5 := by exact LE.le.eq_or_lt' gt
              rcases n_lower with eq|gt
              · simp [eq, segment, size, binaryRec] at n_ne_envelope_segment
              · replace gt : n ≥ 6 := by exact gt
                replace n_lower : n = 6 ∨ n > 6 := by exact LE.le.eq_or_lt' gt
                rcases n_lower with eq|gt
                · simp [eq, segment, size, binaryRec] at n_ne_envelope_segment
                · replace gt : n ≥ 7 := by exact gt
                  exact gt
          clear n_ge_4
          replace n_ge_7 : n = 7 ∨ n > 7 := by exact LE.le.eq_or_lt' n_ge_7
          rcases n_ge_7 with n_eq_7|n_ge_8
          · simp [n_eq_7, size, binaryRec, trailing_zeros]
          · replace n_ge_8 : n ≥ 8 := by exact n_ge_8
            have nsize_ge_4 : n.size ≥ 4 := by
              have s1 : n.size ≥ (8 : ℕ).size := by exact size_le_size n_ge_8
              have s2 : (8 : ℕ).size = 4 := by simp [size, binaryRec]
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
                        · exact Nat.one_lt_two_pow (Nat.sub_ne_zero_iff_lt.mpr (lt_of_add_left_lt nsize_ge_4))
                      simp [this] at x
                      replace : n.size - 1 + 1 = n.size := by grind
                      simp [this] at x
                      exact x
                    simp [x] at add1
                  refine same_n1size_iff_not_pow2.mp ?_
                  · simp [add1] at at_seg_beg
                    exact at_seg_beg
              have n1_is_pow2 : ¬n + 1 = 2 ^ n.size := same_n1size_iff_not_pow2.mpr n1size_eq_nsize
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
              -- envelope segmentを省くとは?
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
                          simp
                          exact nsize_ge_4
                    simp [this]
                  · rename' eq => n_ne_pow2 
                    have s2 : segment (2 ^ (n.size - 2)) ≤ 2 ^ ((2 ^ (n.size - 2) + 1).size - 1) := by
                      exact segment_limit2 (le_pow (zero_lt_sub_of_lt (lt_of_add_left_lt n2size_gt_3)))
                    have s3 : (2 ^ (n.size - 2) + 1).size = n.size - 2 + 1 := by
                       refine size_add ?_ ?_  
                       · exact Nat.one_pos
                       · refine Nat.one_lt_two_pow_iff.mpr ?_
                         · refine Nat.sub_ne_zero_iff_lt.mpr ?_
                           · exact lt_of_add_left_lt n2size_gt_3
                    simp [s3] at s2
                    have seg_limit : segment (n - (2 ^ (n.size - 1) - 1)) < 2 ^ (n.size - 2) := by
                      have concept1 : segment (n / 2) ≤ 2 ^ (n.size - 2) := by
                        have s1 : segment (n / 2) ≤ 2 ^ ((n / 2 + 1).size - 1) := by
                          refine segment_limit2 ?_
                          · refine (Nat.le_div_iff_mul_le ?_).mpr ?_
                            · exact Nat.zero_lt_two
                            · exact le_of_add_left_le n_ge_8
                        have s2 : (n / 2 + 1).size = n.size - 1 := by
                          have : n / 2 < 2 ^ (n.size - 1) := by
                            sorry
                          by_cases even : Even n
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

end LubySegment
