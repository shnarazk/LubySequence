import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

def trailing_zero (n : Nat) : Nat :=
  if h : n < 2
  then (1 - n)
  else if n % 2 = 0 then 1 + trailing_zero (n / 2) else 0

def trailing_ones (n : Nat) : Nat :=
  if h : n < 2
  then n
  else if n % 2 = 1 then 1 + trailing_ones (n / 2) else 0

#eval List.range 9 |>.map trailing_zero

def trailing_one (n : Nat) : Nat :=
  if h : n < 2
  then n
  else if n % 2 = 0 then 0 else 1 + trailing_one (n / 2)

#eval List.range 9 |>.map trailing_one

def scanList {α : Type _} (f : α → α) (init : α) (n : Nat) (start : Bool := true) : List α :=
  match n with
  | 0      => []
  | n' + 1 =>
    let nxt := f init
    if start
      then init :: nxt :: scanList f nxt n' false
      else nxt :: scanList f nxt n' false

#eval scanList (· + 1) 10 8

theorem self_ne_pow_two_succ_of_size (n : Nat) : n < 2 ^ n.size.succ := by
  refine Nat.size_le.mp ?_
  grind

theorem mod_gt_right (a b : Nat) (h : 0 < b) : a % b < b := by exact Nat.mod_lt a h
theorem mod_eq_left (a b : Nat) (ha : a < b) : a % b = a := by exact Nat.mod_eq_of_lt ha

theorem mod_gt_right' (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a % b = 0 → (a - 1) % b + 1 = b := by
  intro h
  simp [←Nat.dvd_iff_mod_eq_zero] at h
  have s1 : (a / b) * b = a := by exact Nat.div_mul_cancel h
  have s2 : (a / b) * b = (a / b - 1) * b + b := by
    calc
      (a / b) * b = (a / b + 1 - 1) * b := by exact rfl
      _ = (a / b - 1 + 1) * b := by
        refine (Nat.mul_right_cancel_iff hb).mpr ?_
        refine Nat.sub_add_comm ?_
        have tf : a / b = 0 ∨ ¬(a / b = 0) := by exact eq_or_ne _ _
        rcases tf with t|f
        {
          have a0 : a = 0 := by exact Nat.eq_zero_of_dvd_of_div_eq_zero h t
          have : ¬ 0 < a := by exact Eq.not_gt a0
          exact absurd ha this
        }
        {
          have : 1 ≤ a / b := by exact Nat.one_le_iff_ne_zero.mpr f
          exact this
        }
      _ = (a / b - 1) * b + 1 * b := by exact Nat.add_mul (a / b - 1) 1 b
      _ = (a / b - 1) * b + b := by grind
  rw [←s1, s2]
  have : (a / b - 1) * b + b - 1 = (a / b - 1) * b + (b - 1) := by
    exact Nat.add_sub_assoc hb ((a / b - 1) * b)
  simp [this]
  grind

theorem mod_gt_right'' (a b : Nat) (ha : 0 < a) (hb : 0 < b) (h1 : a % b ≠ 0) :
    (a - 1) % b + 1 < b := by
  sorry
