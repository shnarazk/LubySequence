module

import Mathlib.Tactic

open Finset Nat

/--
Generates a list by repeatedly applying function `f` starting from `init` for `n` iterations.
If `start` is true, includes the initial value in the result.
-/
@[expose]
public def scanList {α : Type _} (f : α → α) (init : α) (n : ℕ) (start : Bool := true) : List α :=
  match n with
  | 0      => []
  | n' + 1 =>
    let nxt := f init
    if start
      then init :: nxt :: scanList f nxt n' false
      else nxt :: scanList f nxt n' false

-- #eval scanList (· + 1) 10 8

/--
The remainder of division by a positive number is strictly less than the divisor.
-/
public theorem mod_gt_right (a b : ℕ) (h : 0 < b) : a % b < b := by exact mod_lt a h
/--
When a number is smaller than the divisor, the remainder equals the original number.
-/
public theorem mod_eq_left {a b : ℕ} (ha : a < b) : a % b = a := by exact mod_eq_of_lt ha

/--
For positive numbers a and b, if a is divisible by b, then (a-1) % b + 1 = b.
-/
theorem mod_gt_right' {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : a % b = 0 → (a - 1) % b + 1 = b := by
  intro h
  simp [←dvd_iff_mod_eq_zero] at h
  have s1 : (a / b) * b = a := by exact Nat.div_mul_cancel h
  have s2 : (a / b) * b = (a / b - 1) * b + b := by
    calc
      (a / b) * b = (a / b + 1 - 1) * b := by exact rfl
      _ = (a / b - 1 + 1) * b := by
        refine (Nat.mul_right_cancel_iff hb).mpr ?_
        refine Nat.sub_add_comm ?_
        have tf : a / b = 0 ∨ ¬(a / b = 0) := by exact eq_or_ne _ _
        rcases tf with t|f
        · have a0 : a = 0 := by exact eq_zero_of_dvd_of_div_eq_zero h t
          have : ¬ 0 < a := by exact Eq.not_gt a0
          exact absurd ha this
        · have : 1 ≤ a / b := by exact one_le_iff_ne_zero.mpr f
          exact this
      _ = (a / b - 1) * b + 1 * b := by exact add_mul (a / b - 1) 1 b
      _ = (a / b - 1) * b + b := by grind
  rw [←s1, s2]
  have : (a / b - 1) * b + b - 1 = (a / b - 1) * b + (b - 1) := by
    exact Nat.add_sub_assoc hb ((a / b - 1) * b)
  simp [this]
  grind

/--
Converse of mod_gt_right': if (a-1) % b + 1 = b, then a is divisible by b.
-/
theorem mod_gt_right'_mpr {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a - 1) % b + 1 = b → a % b = 0 := by
  by_contra h
  simp at h
  rcases h with ⟨h1,h2⟩
  let a0 := a - 1
  have a0p : a0 = value_of% a0 := by rfl
  have ap' : a = a0 + 1 := by exact (Nat.sub_eq_iff_eq_add ha).mp a0p
  let b0 := b - 1
  have b0p : b0 = value_of% b0 := by rfl
  have bp' : b = b0 + 1 := by exact (Nat.sub_eq_iff_eq_add hb).mp b0p
  simp [ap',bp'] at h1 h2
  have cn : ¬a0 % b0 = 0 := by
    have r := @succ_mod_succ_eq_zero_iff a0 b0
    have (a b : Prop) (h : ¬a) : (b ↔ a) → ¬b := by exact (@iff_false_right a b h).mp
    have s := this ((a0 + 1) % (b0 + 1) = 0) (a0 % (b0 + 1) = b0)
    exact False.elim (this ((a0 + 1) % (b0 + 1) = 0) (a0 % (b0 + 1) = b0) h2 (id (Iff.symm r)) h1)
  have : (a0 + 1) % (b0 + 1) = 0 := by exact succ_mod_succ_eq_zero_iff.mpr h1
  exact absurd this h2

/--
For any natural number a and positive b, (a-1) % b + 1 ≤ b.
-/
public theorem mod_gt_right'' {b : ℕ} (a : ℕ) (hb : 0 < b) : (a - 1) % b + 1 ≤ b := by
  refine add_le_of_le_sub hb ?_
  · refine le_sub_one_of_lt ?_
    · exact mod_gt_right (a - 1) b hb

/--
If a is not divisible by b, then (a-1) % b + 1 < b.
-/
theorem mod_gt_right''' {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h1 : a % b ≠ 0) :
    (a - 1) % b + 1 < b := by
  have el : (a - 1) % b + 1 = b ∨ (a - 1) % b + 1 < b := by
    exact eq_or_lt_of_le (mod_gt_right'' a hb)
  rcases el with e|l
  · apply mod_gt_right'_mpr ha hb at e
    grind
  · exact l
