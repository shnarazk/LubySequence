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

theorem mod_gt_right' (a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    a % b = 0 → (a - 1) % b + 1 = b := by
  intro h
  simp [←Nat.dvd_iff_mod_eq_zero] at h
  
  sorry

theorem mod_gt_right'' (a b : Nat) (ha : 0 < a) (hb : 0 < b) (h1 : a % b ≠ 0) :
    (a - 1) % b + 1 < b := by
  sorry
