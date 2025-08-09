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

theorem bitslength_eq_size (n : Nat) : n.bits.length = n.size := by
  exact Nat.size_eq_bits_len n

theorem bits_of_double_eq_cons_false_and_bits (n : Nat) (h : n > 0) :
    (2 * n).bits = false :: n.bits := by
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt h
  exact Nat.bit0_bits n this

theorem size_of_double_eq_self_add_one (n : Nat) (h : n > 0) : (2 * n).size = n.size + 1 := by
  have h : (2 * n).bits = false :: n.bits := by
    exact bits_of_double_eq_cons_false_and_bits n h
  have t1 : (2 * n).bits.length = (false :: n.bits).length := by
    exact congrArg List.length h
  have t2 : (false :: n.bits).length = n.bits.length + 1 := by
    exact rfl
  simp [t2, bitslength_eq_size] at t1
  exact t1

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
  simp [bitslength_eq_size] at s3
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
  have s3 : (2 * n).bits.length = 1 + n.bits.length := by simp only [s1, s2]
  simp [bitslength_eq_size] at s3
  simp [s3]

theorem bitslength_of_pow2_eq_self_add_one  (n : Nat) : (2 ^ n).bits.length = n + 1 := by
  induction' n with n hn
  { simp }
  {
    have p : 0 < 2 ^ n := by exact Nat.two_pow_pos n
    let v := (2 ^ n).bits
    have vp : v = value_of% v := by exact rfl
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by grind
    simp [this]
    exact hn
  }

theorem size_of_pow2_eq_self_add_one  (n : Nat) : (2 ^ n).size = n + 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_of_pow2_eq_self_add_one n

theorem pow2_bit {n : Nat} : (2 ^ n).bits = List.iterate (·) false n ++ [true] := by
  induction' n with n hn
  { simp }
  {
    have s1 : 2 ^ (n + 1) = 2 * (2 ^ n) := by exact Nat.pow_succ'
    simp [s1]
    exact hn
  }

theorem pow2_sub_one {n : Nat} : (2 ^ n - 1).bits = List.iterate (·) true n := by
  induction' n with n hn
  { simp }
  {
    have s1 : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      calc
        2 ^ (n + 1) - 1 = 2 * 2 ^ n - 1 := by grind
        _ = 2 * 2 ^ n + 1 - 2 := by exact rfl
        _ = 1 + 2 * 2 ^ n - 2 := by rw [add_comm]
        _ = 1 + 2 * (2 ^ n - 1) := by
          simp [Nat.mul_sub]
          refine Nat.add_sub_assoc ?_ 1
          have : 0 < 2 ^ n := by exact Nat.two_pow_pos n
          grind
        _ = 2 * (2 ^ n - 1) + 1 := by rw [add_comm]
    simp [s1]
    exact hn
  }

@[deprecated "Use `size_add` instead of `bitslength_add`" (since := "2025-08-10")]
theorem bitslength_add {n k : Nat} (ha : 0 < k) (hb : k < 2 ^ n) :
    (2 ^ n + k).bits.length = n + 1 := by
  have p1 : (2 ^ n).bits.length ≤ (2 ^ n + k).bits.length := by
    have : (2 ^ n).size ≤ (2 ^ n + k).size := by
      refine Nat.size_le_size ?_
      exact Nat.le_add_right (2 ^ n) k
    simp only [←bitslength_eq_size] at this
    exact this
  have p1' : n + 1 ≤ (2 ^ n + k).bits.length := by
    have : (2 ^ n).bits.length = n + 1 := by
      exact bitslength_of_pow2_eq_self_add_one n
    simp [this] at p1
    exact p1
  have p2 : 2 ^ n + k ≤ 2 ^ (n + 1) - 1 := by
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by exact Nat.pow_succ'
    simp [this]
    clear this
    have : 2 * 2 ^ n = 2 ^ n + 2 ^ n := by
      exact Nat.two_mul (2 ^ n)
    simp [this]
    have : 2 ^ n + 2 ^ n - 1 = 2 ^ n - 1 + 2 ^ n := by
      have : 2 ^ n + 2 ^ n - 1 = 2 ^ n + (2 ^ n - 1) := by
        refine Nat.add_sub_assoc ?_ ?_
        grind
      rw [add_comm _ (2 ^ n - 1)] at this
      exact this
    simp [this]
    rw [add_comm]
    refine Nat.add_le_add_iff_right.mpr ?_
    exact Nat.le_sub_one_of_lt hb
  have p2' : (2 ^ n + k).bits.length ≤ n + 1 := by
    have s1 : (2 ^ n + k).bits.length ≤ (2 ^ (n + 1) - 1).bits.length := by
      have : (2 ^ n + k).size ≤ (2 ^ (n + 1) - 1).size := by
        exact Nat.size_le_size p2
      simp [←bitslength_eq_size] at this
      exact this
    have s2 : (2 ^ (n + 1) - 1).bits.length = n + 1 := by
      have : (2 ^ (n + 1) - 1).bits = List.iterate (·) true (n + 1) := by
        exact pow2_sub_one
      simp [this]
    simp [s2] at s1
    exact s1
  have p2'' : (2 ^ n + k).bits.length ≤ n + 1 := by exact p2'
  exact Nat.le_antisymm p2' p1'

theorem size_add {n k : Nat} (ha : 0 < k) (hb : k < 2 ^ n) :
      (2 ^ n + k).size = n + 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_add ha hb

@[deprecated "Use `size_add'` instead of `bitslength_add'`" (since := "2025-08-10")]
theorem bitslength_add' {n k : Nat} (ha : 0 < k) (hb : (n + k).bits.length < n.bits.length + 1) :
    (n + k).bits.length = n.bits.length := by
  have t1 : n < n + k := by exact Nat.lt_add_of_pos_right ha
  have t2 : n.size ≤ (n + k).size := by
    refine Nat.size_le_size ?_
    grind
  simp [←bitslength_eq_size] at t2
  have le : n.bits.length < (n + k).bits.length ∨ n.bits.length = (n + k).bits.length := by
    exact Or.symm (Nat.eq_or_lt_of_le t2)
  rcases le with l|e
  {
    have l' : n.bits.length + 1 ≤ (n + k).bits.length := by exact l
    have l'' : ¬(n + k).bits.length < n.bits.length + 1 := by exact Nat.not_lt.mpr l
    exact absurd hb l''
  }
  { exact id (Eq.symm e) }

theorem size_add' {n k : Nat} (ha : 0 < k) (hb : (n + k).size < n.size + 1) :
    (n + k).size = n.size := by
  simp [←bitslength_eq_size]
  simp [←bitslength_eq_size] at hb
  exact bitslength_add' ha hb

@[deprecated "Use `size_sub` instead of `bitslength_sub`" (since := "2025-08-10")]
theorem bitslength_sub {n k : Nat} (h : 0 < n) (ha : 0 < k) (hb : k ≤ 2 ^ (n - 1)) :
    (2 ^ n - k).bits.length = n := by
  have p1 : 0 < n := by
    have p : 1 ≤ n := by exact h
    have t1 : (1 : Nat).bits.length ≤ n := by
      have : (1 : Nat).size ≤ n.size := by exact Nat.size_le_size h
      simp
      exact p
    simp at t1
    have t2 : 0 < 1 := by grind
    grind

  have r1 : 2 ^ n - 1 ≥ 2 ^ n - k := by grind
  have e1 : (2 ^ n - 1).bits.length = n := by simp [pow2_sub_one]

  have t1 : (2 ^ n - k).bits.length ≤ (2 ^ n - 1).bits.length := by
    have : 2 ^ n - k ≤ 2 ^ n - 1 := by
      exact r1
    have : (2 ^ n - k).size ≤ (2 ^ n - 1).size := by
      exact Nat.size_le_size r1
    simp [←bitslength_eq_size] at this
    exact this
  simp [e1] at t1
  clear e1 r1

  have t2 : n ≤ (2 ^ n - k).bits.length := by
    have r2 : 2 ^ n - 2 ^ (n - 1) ≤ 2 ^ n - k := by
      exact Nat.sub_le_sub_left hb (2 ^ n)
    have r2' : (2 ^ n - 2 ^ (n - 1)).bits.length ≤ (2 ^ n - k).bits.length := by
      have : (2 ^ n - 2 ^ (n - 1)).size ≤ (2 ^ n - k).size := by
        exact Nat.size_le_size r2
      simp [←bitslength_eq_size] at this
      exact this
    clear r2
    have e2 : 2 ^ n - 2 ^ (n - 1) = 2 ^ (n - 1) := by
      have step1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
        refine Eq.symm (mul_pow_sub_one (by grind) 2)
      simp [step1]
      have step2 : 2 * 2 ^ (n - 1) - 2 ^ (n - 1) = 2 ^ (n - 1) := by
        calc
          2 * 2 ^ (n - 1) - 2 ^ (n - 1) = 2 * 2 ^ (n - 1) - 1 * 2 ^ (n - 1) := by
            have : 2 ^ (n - 1) = 1 * 2 ^ (n - 1) := by
              exact Eq.symm (Nat.one_mul (2 ^ (n - 1)))
            nth_rewrite 2 [this]
            exact rfl
          _ = (2 - 1) * 2 ^ (n - 1) := by
             exact Eq.symm (Nat.sub_mul 2 1 (2 ^ (n - 1)))
          _ = 2 ^ (n - 1) := by
            refine (Nat.mul_eq_right ?_).mpr rfl
            exact Ne.symm (NeZero.ne' (2 ^ (n - 1)))
      simp [step2]
    have e2' : (2 ^ n - 2 ^ (n - 1)).bits.length = (2 ^ (n - 1)).bits.length := by
      have : (2 ^ n - 2 ^ (n - 1)).size = (2 ^ (n - 1)).size := by
        exact congrArg Nat.size e2
      simp [←bitslength_eq_size] at this
      exact this
    clear e2
    simp [e2'] at r2'
    clear e2'
    have e3 : (2 ^ (n - 1)).bits.length = n := by
      have step1 : (2 ^ (n - 1)).bits.length = n - 1 + 1 := by
        exact bitslength_of_pow2_eq_self_add_one (n - 1)
      have step2 : n - 1 + 1 = n := by
        exact Nat.sub_add_cancel p1
      simp [step2] at step1
      exact step1
    simp [e3] at r2'
    exact r2'
  exact Nat.le_antisymm t1 t2

theorem size_sub {n k : Nat} (h : 0 < n) (ha : 0 < k) (hb : k ≤ 2 ^ (n - 1)) :
      (2 ^ n - k).size = n := by
  simp [←bitslength_eq_size]
  exact bitslength_sub h ha hb

@[deprecated "Use `size_div` instead of `bitslength_div`" (since := "2025-08-10")]
theorem bitslength_div {n : Nat} (h1 : 1 < n) (h2 : 2 ∣ n) :
    (n / 2).bits.length = n.bits.length - 1 := by
  let n2b := (n / 2).bits
  have n2bp : n2b = value_of% n2b := by rfl
  have np : (2 * (n / 2)).bits.length = (n / 2).bits.length + 1 := by
    have s1 : (2 * (n / 2)).bits = false :: (n / 2).bits := by
      refine Nat.bit0_bits (n / 2) (by grind)
    have s2 : (false :: (n / 2).bits).length = 1 + (n / 2).bits.length := by
      exact Nat.succ_eq_one_add (n / 2).bits.length
    simp only [←s1] at s2
    simp [s2]
    exact Nat.add_comm 1 (n / 2).bits.length
  have : 2 * (n /2) = n := by exact Nat.mul_div_cancel' h2
  simp [this] at np
  exact Nat.eq_sub_of_add_eq (id (Eq.symm np))

theorem size_div {n : Nat} (h1 : 1 < n) (h2 : 2 ∣ n) : (n / 2).size = n.size - 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_div h1 h2

theorem bitslength_le_bitslength {a b : Nat} (h : a ≤ b) : a.bits.length ≤ b.bits.length := by
  have t := Nat.size_le_size h
  simp [←bitslength_eq_size] at t
  exact t

theorem le_if_le_size {a b : Nat} : a.size < b.size → a < b := by
  intro h1
  by_contra h2
  simp at h2
  have c1 : b.size ≤ a.size := by exact Nat.size_le_size h2
  have c2 : ¬a.size < b.size := by exact Nat.not_lt.mpr c1
  exact absurd h1 c2

