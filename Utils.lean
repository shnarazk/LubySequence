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
theorem mod_eq_left {a b : Nat} (ha : a < b) : a % b = a := by exact Nat.mod_eq_of_lt ha

theorem mod_gt_right' {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
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

/-
Nat.succ_mod_succ_eq_zero_iff 📋 Init.Data.Nat.Lemmas
{a b : ℕ} : (a + 1) % (b + 1) = 0 ↔ a % (b + 1) = b
-/

theorem mod_gt_right'_mpr {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
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
    have r := @Nat.succ_mod_succ_eq_zero_iff a0 b0
    have (a b : Prop) (h : ¬a) : (b ↔ a) → ¬b := by exact (@iff_false_right a b h).mp
    have s := this ((a0 + 1) % (b0 + 1) = 0) (a0 % (b0 + 1) = b0) 
    exact False.elim (this ((a0 + 1) % (b0 + 1) = 0) (a0 % (b0 + 1) = b0) h2 (id (Iff.symm r)) h1)
  have : (a0 + 1) % (b0 + 1) = 0 := by exact Nat.succ_mod_succ_eq_zero_iff.mpr h1
  exact absurd this h2
  
theorem mod_gt_right'' {b : Nat} (a : Nat) (hb : 0 < b) : (a - 1) % b + 1 ≤ b := by
  refine Nat.add_le_of_le_sub hb ?_
  refine Nat.le_sub_one_of_lt ?_
  exact mod_gt_right (a - 1) b hb

theorem mod_gt_right''' {a b : Nat} (ha : 0 < a) (hb : 0 < b) (h1 : a % b ≠ 0) :
    (a - 1) % b + 1 < b := by
  have el : (a - 1) % b + 1 = b ∨ (a - 1) % b + 1 < b := by
    exact Nat.eq_or_lt_of_le (mod_gt_right'' a hb)
  rcases el with e|l
  {
    apply mod_gt_right'_mpr ha hb at e
    grind
  }
  exact l

theorem length_of_bits_eq_size (n : Nat) : n.bits.length = n.size := by
  exact Nat.size_eq_bits_len n

theorem bits_of_double_eq_cons_false_and_bits (n : Nat) (h : n > 0) :
    (2 * n).bits = false :: n.bits := by
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt h
  exact Nat.bit0_bits n this

example (n : Nat) : (2 * n + 1).bits = true :: n.bits := by
  exact Nat.bit1_bits n

theorem size_of_two_mul_eq_aize_add_one (n : Nat) (h : n > 0) :
    n.size + 1 = (n * 2).size := by
  simp [←Nat.size_eq_bits_len, Nat.mul_comm n 2, bits_of_double_eq_cons_false_and_bits n h]

theorem size_lt {a b : Nat} (h : 0 < a) : 2 * a < b → a.size < b.size := by
  intro hg
  have s1 : (2 * a).bits = false :: a.bits := by refine Nat.bit0_bits a (by grind) 
  have s2 : (false :: a.bits).length = 1 + a.bits.length := by
    exact Nat.succ_eq_one_add a.bits.length
  have s3 :(2 * a).bits.length = 1 + a.bits.length := by simp only [s1, s2]
  simp [length_of_bits_eq_size] at s3
  have stricten (a b c : Nat) (h : 0 < b) : (a + b = c) → (a < c) := by
    have le := @Nat.le.intro a c b
    intro hh
    have le' := le hh
    clear le
    have tf : a < c ∨ a = c := by exact Or.symm (Nat.eq_or_lt_of_le le')
    clear le'
    rcases tf with t|f
    { expose_names ; exact t }
    {
      expose_names
      simp [f] at hh
      have : ¬b = 0 := by exact Nat.ne_zero_of_lt h
      exact absurd hh this
    }
  have tr1 : a.size < (2 * a).size := by
    exact stricten a.size 1 (2 * a).size (by grind) (by grind)
  have hg' : 2 * a ≤ b := by exact Nat.le_of_succ_le hg
  have tr2 : (2 * a).size ≤ b.size := by refine Nat.size_le_size hg'
  exact Nat.lt_of_lt_of_le tr1 tr2
    
theorem pow_two_of_size_le_self {n : Nat} (h : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  refine Nat.lt_size.mp ?_
  have s1 : (2 * n).bits = false :: n.bits := by refine Nat.bit0_bits n (by grind) 
  have s2 : (false :: n.bits).length = 1 + n.bits.length := by
    exact Nat.succ_eq_one_add n.bits.length
  have s3 :(2 * n).bits.length = 1 + n.bits.length := by simp only [s1, s2]
  simp [length_of_bits_eq_size] at s3
  simp [s3]

  

