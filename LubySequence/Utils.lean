import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

open Finset Nat

/--
The size (bit length) of the natural number 2 is 2.
-/
@[simp]
theorem size2_eq_2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]

/--
The size (bit length) of the natural number 3 is 2.
-/
@[simp]
theorem size3_eq_2 : (3 : ℕ).size = 2 := by simp [size, binaryRec]

/--
The size (bit length) of the natural number 4 is 3.
-/
@[simp]
theorem size4_eq_3 : (4 : ℕ).size = 3 := by simp [size, binaryRec]

/--
For any natural number n ≥ 2, its size (bit length) is at least 2.
-/
@[simp]
theorem size2_ge_2 {n : ℕ} (h : n ≥ 2) : n.size ≥ 2 := by
  have s1 : n.size ≥ (2 : ℕ).size := by exact size_le_size h
  simp at s1
  exact s1

/--
For any natural number n, the size of n + 2 is at least 2.
-/
@[simp]
theorem size0_add_2_ge_2 (n : ℕ) : (n + 2).size ≥ 2 := by
  have s1 : n ≥ 0 := by exact Nat.zero_le n
  have s2 : n + 2 ≥ 0 + 2 := by exact Nat.add_le_add_right s1 2
  exact size2_ge_2 s2

/--
For any natural number n ≥ 2, the size of n + 2 is at least 3.
-/
@[simp]
theorem size2_add_2_ge_2 {n : ℕ} (h : n ≥ 2) : (n + 2).size ≥ 3 := by
  have s1 : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right h 2
  have s2 : (n + 2).size ≥ (2 + 2).size := by exact size_le_size s1
  simp at s2
  exact s2

/--
For any natural number n ≥ 4, the size of n is at least 3.
-/
@[simp]
theorem size4_add_0_ge_2 {n : ℕ} (h : n ≥ 4) : n.size ≥ 3 := by
  have s1 : n.size ≥ (4 : ℕ).size := by exact size_le_size h
  simp at s1
  exact s1

/--
Returns the number of zeros at the end of bit representation of Nat `n`.
Note: `trailing_zeros 0 = 0`
It differs from the Rust implementation which returns 64 if n = 0_u64.
-/
def trailing_zeros (n : ℕ) : ℕ := match h : n with
  | 0      => n
  | n' + 1 =>
    if n = 2 ^ (n.size - 1)
    then n.size - 1
    else
      have decreasing : n - 2 ^ (n.size - 1) < n := by
        expose_names
        have n1 : n > 0 := by exact Nat.lt_of_sub_eq_succ h
        have t1 : 0 < 2 ^ (n.size - 1) := by exact Nat.two_pow_pos (n.size - 1)
        exact sub_lt n1 t1
      trailing_zeros (n - 2 ^ (n.size - 1))
  -- | _ => if n < 2 then 0 else if n % 2 = 0 then 1 + trailing_zeros (n / 2) else 0

-- #eval List.range 9 |>.map (fun n ↦ (n, trailing_zeros n))

/--
Returns the number of consecutive ones at the end of bit representation of Nat `n`.
For example, `trailing_ones 7 = 3` since 7 in binary is 111.
-/
def trailing_ones (n : ℕ) : ℕ :=
  if h : n < 2
  then n
  else if n % 2 = 1 then 1 + trailing_ones (n / 2) else 0

/--
Generates a list by repeatedly applying function `f` starting from `init` for `n` iterations.
If `start` is true, includes the initial value in the result.
-/
def scanList {α : Type _} (f : α → α) (init : α) (n : ℕ) (start : Bool := true) : List α :=
  match n with
  | 0      => []
  | n' + 1 =>
    let nxt := f init
    if start
      then init :: nxt :: scanList f nxt n' false
      else nxt :: scanList f nxt n' false

-- #eval scanList (· + 1) 10 8

/--
Every natural number is strictly less than 2 raised to the power of its size plus one.
-/
theorem self_ne_pow_two_succ_of_size (n : ℕ) : n < 2 ^ n.size.succ := by exact size_le.mp (by grind)

/--
The remainder of division by a positive number is strictly less than the divisor.
-/
theorem mod_gt_right (a b : ℕ) (h : 0 < b) : a % b < b := by exact mod_lt a h
/--
When a number is smaller than the divisor, the remainder equals the original number.
-/
theorem mod_eq_left {a b : ℕ} (ha : a < b) : a % b = a := by exact mod_eq_of_lt ha

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
theorem mod_gt_right'' {b : ℕ} (a : ℕ) (hb : 0 < b) : (a - 1) % b + 1 ≤ b := by
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

/--
The length of the bit representation equals the size of a natural number.
-/
theorem bitslength_eq_size (n : ℕ) : n.bits.length = n.size := by exact size_eq_bits_len n

/--
The bit representation of 2*n is false (0) prepended to the bit representation of n.
-/
theorem bits_of_double_eq_cons_false_and_bits (n : ℕ) (h : n > 0) :
    (2 * n).bits = false :: n.bits := by
  have : n ≠ 0 := by exact ne_zero_of_lt h
  exact bit0_bits n this

/--
The size of 2*n is one more than the size of n (for positive n).
-/
theorem size_of_double_eq_self_add_one (n : ℕ) (h : n > 0) : (2 * n).size = n.size + 1 := by
  have h : (2 * n).bits = false :: n.bits := by
    exact bits_of_double_eq_cons_false_and_bits n h
  have t1 : (2 * n).bits.length = (false :: n.bits).length := by
    exact congrArg List.length h
  have t2 : (false :: n.bits).length = n.bits.length + 1 := by
    exact rfl
  simp [t2, bitslength_eq_size] at t1
  exact t1

/--
For n ≥ 2 and k < 2^n, adding k to 2^n does not change the bit size.
In other words, (2^n + k).size = (2^n).size when k is strictly less than 2^n.
-/
theorem size_of_pow2 {k n : ℕ} (h2 : k < 2 ^ n) :
    (2 ^ n + k).size = (2 ^ n).size := by
  have s1 : (2 ^ n + k).size ≤ n + 1 := by
    have : 2 ^ n + k < 2 ^ (n + 1) := by
      have t1 : 2 ^ n + k < 2 ^ n + 2 ^ n := by exact Nat.add_lt_add_left h2 (2 ^ n)
      have t2 : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by exact Eq.symm (two_pow_succ n)
      simp [t2] at t1
      exact t1
    exact size_le.mpr this
  have s2 : (2 ^ n).size = n + 1 := by exact size_pow
  simp [←s2] at s1
  have s3 : (2 ^ n + k).size ≥ (2 ^ n).size := by
    exact size_le_size (Nat.le_add_right (2 ^ n) k)
  exact Nat.le_antisymm s1 s3

/--
The bit representation of 2*n + 1 is true (1) prepended to the bit representation of n.
-/
example (n : ℕ) : (2 * n + 1).bits = true :: n.bits := by
  exact bit1_bits n

/--
The size of n*2 equals n.size + 1 (for positive n).
-/
theorem size_of_two_mul_eq_aize_add_one (n : ℕ) (h : n > 0) :
    n.size + 1 = (n * 2).size := by
  simp [←size_eq_bits_len, mul_comm n 2, bits_of_double_eq_cons_false_and_bits n h]

/--
If 2*a < b, then the size of a is less than the size of b.
-/
theorem size_lt {a b : ℕ} (h : 0 < a) : 2 * a < b → a.size < b.size := by
  intro hg
  have s1 : (2 * a).bits = false :: a.bits := by refine bit0_bits a (by grind)
  have s2 : (false :: a.bits).length = 1 + a.bits.length := by
    exact succ_eq_one_add a.bits.length
  have s3 :(2 * a).bits.length = 1 + a.bits.length := by simp only [s1, s2]
  simp [bitslength_eq_size] at s3
  have stricten (a b c : ℕ) (h : 0 < b) : (a + b = c) → (a < c) := by
    have le := @le.intro a c b
    intro hh
    have le' := le hh
    clear le
    have tf : a < c ∨ a = c := by exact Or.symm (eq_or_lt_of_le le')
    clear le'
    rcases tf with t|f
    · expose_names ; exact t
    · expose_names
      simp [f] at hh
      have : ¬b = 0 := by exact ne_zero_of_lt h
      exact absurd hh this
  have tr1 : a.size < (2 * a).size := by
    exact stricten a.size 1 (2 * a).size (by grind) (by grind)
  have hg' : 2 * a ≤ b := by exact le_of_succ_le hg
  have tr2 : (2 * a).size ≤ b.size := by refine size_le_size hg'
  exact lt_of_lt_of_le tr1 tr2

/--
For positive n, 2^(n.size) ≤ 2*n.
-/
theorem pow_two_of_size_le_self {n : ℕ} (h : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  refine lt_size.mp ?_
  have s1 : (2 * n).bits = false :: n.bits := by refine bit0_bits n (by grind)
  have s2 : (false :: n.bits).length = 1 + n.bits.length := by
    exact succ_eq_one_add n.bits.length
  have s3 : (2 * n).bits.length = 1 + n.bits.length := by simp only [s1, s2]
  simp [bitslength_eq_size] at s3
  simp [s3]

/--
The bit representation length of 2^n equals n+1.
-/
theorem bitslength_of_pow2_eq_self_add_one  (n : ℕ) : (2 ^ n).bits.length = n + 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    have p : 0 < 2 ^ n := by exact Nat.two_pow_pos n
    let v := (2 ^ n).bits
    have vp : v = value_of% v := by exact rfl
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by grind
    simp [this]
    exact hn

/--
The size of 2^n equals n+1.
-/
theorem size_of_pow2_eq_self_add_one  (n : ℕ) : (2 ^ n).size = n + 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_of_pow2_eq_self_add_one n

/--
The bit representation of 2^n consists of n false bits followed by one true bit.
-/
theorem pow2_bit {n : ℕ} : (2 ^ n).bits = List.iterate (·) false n ++ [true] := by
  induction n with
  | zero => simp
  | succ n hn =>
    have s1 : 2 ^ (n + 1) = 2 * (2 ^ n) := by exact pow_succ'
    simp [s1]
    exact hn

/--
The bit representation of 2^n - 1 consists of n true bits.
-/
theorem pow2_sub_one {n : ℕ} : (2 ^ n - 1).bits = List.iterate (·) true n := by
  induction n with
  | zero => simp
  | succ n hn =>
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

/--
For 0 < k < 2^n, the bit length of 2^n + k equals n+1.
-/
@[deprecated "Use `size_add` instead of `bitslength_add`" (since := "2025-08-10")]
theorem bitslength_add {n k : ℕ} (ha : 0 < k) (hb : k < 2 ^ n) :
    (2 ^ n + k).bits.length = n + 1 := by
  have p1 : (2 ^ n).bits.length ≤ (2 ^ n + k).bits.length := by
    have : (2 ^ n).size ≤ (2 ^ n + k).size := by
      refine size_le_size ?_
      exact le_add_right (2 ^ n) k
    simp only [←bitslength_eq_size] at this
    exact this
  have p1' : n + 1 ≤ (2 ^ n + k).bits.length := by
    have : (2 ^ n).bits.length = n + 1 := by
      exact bitslength_of_pow2_eq_self_add_one n
    simp [this] at p1
    exact p1
  have p2 : 2 ^ n + k ≤ 2 ^ (n + 1) - 1 := by
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by exact pow_succ'
    simp [this]
    clear this
    have : 2 * 2 ^ n = 2 ^ n + 2 ^ n := by
      exact two_mul (2 ^ n)
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
    exact le_sub_one_of_lt hb
  have p2' : (2 ^ n + k).bits.length ≤ n + 1 := by
    have s1 : (2 ^ n + k).bits.length ≤ (2 ^ (n + 1) - 1).bits.length := by
      have : (2 ^ n + k).size ≤ (2 ^ (n + 1) - 1).size := by
        exact size_le_size p2
      simp [←bitslength_eq_size] at this
      exact this
    have s2 : (2 ^ (n + 1) - 1).bits.length = n + 1 := by
      have : (2 ^ (n + 1) - 1).bits = List.iterate (·) true (n + 1) := by
        exact pow2_sub_one
      simp [this]
    simp [s2] at s1
    exact s1
  have p2'' : (2 ^ n + k).bits.length ≤ n + 1 := by exact p2'
  exact le_antisymm p2' p1'

/--
For 0 < k < 2^n, the size of 2^n + k equals n+1.
-/
theorem size_add {n k : ℕ} (ha : 0 < k) (hb : k < 2 ^ n) : (2 ^ n + k).size = n + 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_add ha hb

/--
If adding k to n doesn't increase the bit length beyond n.bits.length, then the bit length stays the same.
-/
@[deprecated "Use `size_add'` instead of `bitslength_add'`" (since := "2025-08-10")]
theorem bitslength_add' {n k : ℕ} (ha : 0 < k) (hb : (n + k).bits.length < n.bits.length + 1) :
    (n + k).bits.length = n.bits.length := by
  have t1 : n < n + k := by exact Nat.lt_add_of_pos_right ha
  have t2 : n.size ≤ (n + k).size := by
    refine size_le_size ?_
    grind
  simp [←bitslength_eq_size] at t2
  have le : n.bits.length < (n + k).bits.length ∨ n.bits.length = (n + k).bits.length := by
    exact Or.symm (eq_or_lt_of_le t2)
  rcases le with l|e
  · have l' : n.bits.length + 1 ≤ (n + k).bits.length := by exact l
    have l'' : ¬(n + k).bits.length < n.bits.length + 1 := by exact not_lt.mpr l
    exact absurd hb l''
  · exact id (Eq.symm e)

/--
If adding k to n doesn't increase the size beyond n.size, then the size stays the same.
-/
theorem size_add' {n k : ℕ} (ha : 0 < k) (hb : (n + k).size < n.size + 1) : (n + k).size = n.size := by
  simp [←bitslength_eq_size]
  simp [←bitslength_eq_size] at hb
  exact bitslength_add' ha hb

/--
For n > 0 and 0 < k ≤ 2^(n-1), the bit length of 2^n - k equals n.
-/
@[deprecated "Use `size_sub` instead of `bitslength_sub`" (since := "2025-08-10")]
theorem bitslength_sub {n k : ℕ} (h : 0 < n) (ha : 0 < k) (hb : k ≤ 2 ^ (n - 1)) :
    (2 ^ n - k).bits.length = n := by
  have p1 : 0 < n := by
    have p : 1 ≤ n := by exact h
    have t1 : (1 : ℕ).bits.length ≤ n := by
      have : (1 : ℕ).size ≤ n.size := by exact size_le_size h
      simp
      exact p
    simp at t1
    have t2 : 0 < 1 := by grind
    grind
  have r1 : 2 ^ n - 1 ≥ 2 ^ n - k := by grind
  have e1 : (2 ^ n - 1).bits.length = n := by simp [pow2_sub_one]
  have t1 : (2 ^ n - k).bits.length ≤ (2 ^ n - 1).bits.length := by
    have : 2 ^ n - k ≤ 2 ^ n - 1 := by exact r1
    have : (2 ^ n - k).size ≤ (2 ^ n - 1).size := by exact size_le_size r1
    simp [←bitslength_eq_size] at this
    exact this
  simp [e1] at t1
  clear e1 r1
  have t2 : n ≤ (2 ^ n - k).bits.length := by
    have r2 : 2 ^ n - 2 ^ (n - 1) ≤ 2 ^ n - k := by exact Nat.sub_le_sub_left hb (2 ^ n)
    have r2' : (2 ^ n - 2 ^ (n - 1)).bits.length ≤ (2 ^ n - k).bits.length := by
      have : (2 ^ n - 2 ^ (n - 1)).size ≤ (2 ^ n - k).size := by exact size_le_size r2
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
              exact Eq.symm (one_mul (2 ^ (n - 1)))
            rewrite (occs := .pos [2]) [this]
            exact rfl
          _ = (2 - 1) * 2 ^ (n - 1) := by
             exact Eq.symm (Nat.sub_mul 2 1 (2 ^ (n - 1)))
          _ = 2 ^ (n - 1) := by
            refine (mul_eq_right ?_).mpr rfl
            exact Ne.symm (NeZero.ne' (2 ^ (n - 1)))
      simp [step2]
    have e2' : (2 ^ n - 2 ^ (n - 1)).bits.length = (2 ^ (n - 1)).bits.length := by
      have : (2 ^ n - 2 ^ (n - 1)).size = (2 ^ (n - 1)).size := by exact congrArg size e2
      simp [←bitslength_eq_size] at this
      exact this
    clear e2
    simp [e2'] at r2'
    clear e2'
    have e3 : (2 ^ (n - 1)).bits.length = n := by
      have step1 : (2 ^ (n - 1)).bits.length = n - 1 + 1 := by
        exact bitslength_of_pow2_eq_self_add_one (n - 1)
      have step2 : n - 1 + 1 = n := by exact Nat.sub_add_cancel p1
      simp [step2] at step1
      exact step1
    simp [e3] at r2'
    exact r2'
  exact le_antisymm t1 t2

/--
For n > 0 and 0 < k ≤ 2^(n-1), the size of 2^n - k equals n.
-/
theorem size_sub {n k : ℕ} (h : 0 < n) (ha : 0 < k) (hb : k ≤ 2 ^ (n - 1)) :
      (2 ^ n - k).size = n := by
  simp [←bitslength_eq_size]
  exact bitslength_sub h ha hb

/--
For n ≥ 1 divisible by 2, the bit length of n/2 is one less than the bit length of n.
-/
@[deprecated "Use `size_div` instead of `bitslength_div`" (since := "2025-08-10")]
theorem bitslength_div {n : ℕ} (h1 : 1 ≤ n) (h2 : 2 ∣ n) :
    (n / 2).bits.length = n.bits.length - 1 := by
  let n2b := (n / 2).bits
  have n2bp : n2b = value_of% n2b := by rfl
  have np : (2 * (n / 2)).bits.length = (n / 2).bits.length + 1 := by
    have s1 : (2 * (n / 2)).bits = false :: (n / 2).bits := by
      refine bit0_bits (n / 2) (by grind)
    have s2 : (false :: (n / 2).bits).length = 1 + (n / 2).bits.length := by
      exact succ_eq_one_add (n / 2).bits.length
    simp only [←s1] at s2
    simp [s2]
    exact add_comm 1 (n / 2).bits.length
  have : 2 * (n /2) = n := by exact Nat.mul_div_cancel' h2
  simp [this] at np
  exact Nat.eq_sub_of_add_eq (id (Eq.symm np))

/--
For n ≥ 1 divisible by 2, the size of n/2 is one less than the size of n.
-/
theorem size_div {n : ℕ} (h1 : 1 ≤ n) (h2 : 2 ∣ n) : (n / 2).size = n.size - 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_div h1 h2

/--
If a ≤ b, then the bit length of a is at most the bit length of b.
-/
theorem bitslength_le_bitslength {a b : ℕ} (h : a ≤ b) : a.bits.length ≤ b.bits.length := by
  have t := size_le_size h
  simp [←bitslength_eq_size] at t
  exact t

/--
If a has a strictly smaller size than b, then a < b.
-/
theorem le_if_le_size {a b : ℕ} : a.size < b.size → a < b := by
  intro h1
  by_contra h2
  simp at h2
  have c1 : b.size ≤ a.size := by exact size_le_size h2
  have c2 : ¬a.size < b.size := by exact not_lt.mpr c1
  exact absurd h1 c2

/--
For any n, the size of `n + 1` is either equal to `n.size` or `n.size + 1`.
-/
theorem size_limit (n : ℕ) : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := by
  by_cases h : n = 0
  · simp [h]
  · replace h : n > 0 := by exact zero_lt_of_ne_zero h
    have s1 : n.size ≤ (n + 1).size := by exact size_le_size (le_add_right n 1)
    have s2 : (n + 1).size ≤ n.size + 1 := by
      have t1 : (2 * n).size = n.size + 1 := by exact size_of_double_eq_self_add_one n h
      have t2 : n + 1 ≤ 2 * n := by exact add_one_le_two_mul h
      have t2' : (n + 1).size ≤ (2 * n).size := by exact size_le_size t2
      simp [t1] at t2'
      exact t2'
    by_contra h'
    push_neg at h'
    rcases h' with ⟨a, b⟩
    have c1 : n.size < (n + 1).size := by exact lt_of_le_of_ne s1 (id (Ne.symm a))
    have c2 : (n + 1).size < n.size + 1 := by exact lt_of_le_of_ne s2 b
    have c2' : (n + 1).size ≤ n.size  := by exact le_of_lt_succ c2
    have c2'' : ¬(n + 1).size > n.size := by exact not_lt.mpr c2'
    exact absurd c1 c2''

/--
Every natural number less than 2^k has size at most k.
-/
theorem pow2_is_minimum (k : ℕ) : ∀ n < 2 ^ k, n.size ≤ k := by
  intro n hn
  have t1 : n.size ≤ (2 ^ k).size := by exact size_le_size (le_of_succ_le hn)
  have t2 : (2 ^ k).size = k + 1 := by exact size_of_pow2_eq_self_add_one k
  simp [t2] at t1
  exact size_le.mpr hn

/--
If n is an "envelope" (n = 2^(n.size) - 1), then incrementing n increases the size by exactly 1.
This characterizes when the bit size increases: it happens precisely at powers of 2 minus 1.
-/
theorem size_of_pow2_eq_size_of_envelope_add_1 {n : ℕ} :
    n = 2 ^ n.size - 1 → (n + 1).size = n.size + 1 := by
  intro n_is_envelope
  rw (occs := .pos [1]) [n_is_envelope]
  have : 2 ^ n.size - 1 + 1 = 2 ^ n.size := by
    exact Nat.sub_add_cancel (Nat.one_le_two_pow)
  simp [this]
  replace : (2 ^ n.size).size = n.size + 1 := by
    exact size_of_pow2_eq_self_add_one n.size
  simp [this]

/--
For positive n equal to 2^(n.size - 1), the size of n is one more than the size of n - 1.
This is a variant characterization showing when a number is exactly a power of 2.
-/
theorem size_of_pow2_eq_size_of_envelope_add_1' {n : ℕ} (h : n > 0) :
    n = 2 ^ (n.size - 1) → n.size = (n - 1).size + 1 := by
  intro n_is_envelope
  have : (n - 1 + 1).size = (n - 1).size ∨ (n - 1 + 1).size = (n - 1).size + 1 := by
    exact size_limit (n - 1)
  have n_mp : n - 1 + 1 = n := by exact Nat.sub_add_cancel h
  have nsize_mp : n.size - 1 + 1 = n.size := by
    refine Nat.sub_add_cancel ?_
    · replace h : n ≥ 1 := by exact h
      have s1 : n.size ≥ (1 : ℕ).size := by exact size_le_size h
      have s2 : (1 : ℕ).size = 1 := by simp [size]
      simp [s2] at s1
      exact s1
  rcases this with eq|gt
  · have s1 : (n - 1).size < n.size := by
      have s1 : n - 1 < 2 ^ (n.size - 1) := by
        rw [←n_is_envelope]
        exact sub_one_lt_of_lt h
      have : (n - 1).size ≤ n.size - 1 := by exact pow2_is_minimum (n.size - 1) (n - 1) s1
      replace : (n - 1).size < n.size - 1 + 1 := by exact Order.lt_add_one_iff.mpr this
      simp [nsize_mp] at this
      exact this
    simp [n_mp] at eq
    simp [eq] at s1
  · simp [n_mp] at gt
    exact gt

/--
For n ≥ 1, n is at least 2^(n.size - 1).
-/
theorem n_ge_subenvelope {n: ℕ} (h : 1 ≤ n) : n ≥ 2 ^ (n.size - 1) := by
  have tf : 1 = n ∨ 1 < n := by exact eq_or_lt_of_le h
  rcases tf with t|f
  · simp [←t]
  · have n2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
    have h1 : 2 ≤ n := by exact f
    have h2 : 2 ≤ n.size := by
      have t1 : (2 : ℕ).size ≤ n.size := by exact size_le_size f
      simp [n2] at t1
      exact t1
    have : n > 2 ^ (n.size - 1) - 1 := by
      have : n.size > (2 ^ (n.size - 1) - 1).size := by
        have : (2 ^ (n.size - 1) - 1).size = n.size - 1 := by
          refine size_sub ?_ (by grind)  ?_
          · exact zero_lt_sub_of_lt h2
          · have : 0 ≤ n.size - 1 - 1 := by
              have t1 : (2 : ℕ).size - 1 - 1 ≤ n.size - 1 - 1 := by
                have : (2 : ℕ).size - 1 ≤ n.size - 1 := by
                  refine Nat.sub_le_sub_right ?_ 1
                  · simp [n2] ; exact h2
                exact Nat.sub_le_sub_right this 1
              simp
            exact Nat.one_le_two_pow
        simp [this]
        exact zero_lt_of_lt h2
      exact le_if_le_size this
    exact le_of_pred_lt this

/--
For positive n, 2^(n.size) ≤ 2*n.
-/
theorem pow2size_has_upper_bound : ∀ n > 0, 2 ^ n.size ≤ 2 * n := by
  exact fun n a ↦ pow_two_of_size_le_self a

/--
The number of trailing zeros in 2^n equals n.
-/
theorem trailing_zeros_of_envelope : ∀ n : ℕ, trailing_zeros (2 ^ n) = n := by
  intro n
  induction n with
  | zero => simp [trailing_zeros.eq_def]
  | succ n hn' =>
    rw [trailing_zeros.eq_def]
    split
    · expose_names ;
      have c : ¬2 ^ (n + 1) = 0 := by exact NeZero.ne (2 ^ (n + 1))
      exact absurd heq c
    · expose_names
      have n2 : (2 ^ (n + 1)).size = n + 2 := by exact size_of_pow2_eq_self_add_one (n + 1)
      split
      · expose_names ; simp [n2]
      · expose_names ; simp [n2] at h

/--
For positive n not equal to 2^(n.size-1), trailing_zeros(n) = trailing_zeros(n - 2^(n.size-1)).
-/
theorem trailing_zeros_prop1 : ∀ n > 0,
    ¬n = 2 ^ (n.size - 1) → trailing_zeros n = trailing_zeros (n - 2 ^ (n.size - 1)) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro n_ne_envenlop
    rw [trailing_zeros.eq_def]
    split
    · contradiction
    · expose_names
      split
      · expose_names ; exact absurd h n_ne_envenlop
      · exact rfl

/--
For positive n and k where 2^k > n, adding 2^k to n preserves the number of trailing zeros.
This shows that adding a sufficiently large power of 2 does not affect trailing zeros.
-/
theorem trailing_zeros_prop1' : ∀ n > 0, ∀ k : ℕ,
    2 ^ k > n → trailing_zeros (n + 2 ^ k) = trailing_zeros n := by
  intro n n_gt_0 k pow2k_gt_n
  rw [trailing_zeros.eq_def]
  split
  · expose_names
    have n_eq_0 : n = 0 := by exact Nat.eq_zero_of_add_eq_zero_right heq
    replace n_gt_0 : ¬n = 0 := by exact Nat.ne_zero_of_lt n_gt_0
    exact absurd n_eq_0 n_gt_0
  · expose_names
    split
    · expose_names
      have : 2 ^ (k + 1) = 2 ^ ((n + 2 ^ k).size - 1) := by
        have : (2 ^ k + n).size = k + 1 := by exact size_add n_gt_0 pow2k_gt_n
        rw (occs := .pos [2]) [add_comm] at h
        simp [this] at h
        replace n_gt_0 : ¬n = 0 := by exact Nat.ne_zero_of_lt n_gt_0
        exact absurd h n_gt_0
      rw (occs := .pos [1]) [←this] at h
      replace : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by exact two_pow_succ k
      simp [this] at h
      have h' : ¬n = 2 ^ k := by exact Nat.ne_of_lt pow2k_gt_n
      exact absurd h h'
    · expose_names
      simp
      have : 2 ^ ((n + 2 ^ k).size - 1) = 2 ^ k := by
        have : (2 ^ k + n).size = k + 1 := by exact size_add n_gt_0 pow2k_gt_n
        rw (occs := .pos [1]) [add_comm] at this
        simp [this]
      simp [this]

/--
For n > 1 where n = 2^(n.size-1), trailing_zeros(n) = trailing_zeros(n - 2^(n.size-2)) + 1.
-/
@[simp]
theorem trailing_zeros_prop2 :
    ∀ n > 1, n = 2 ^ (n.size - 1) → trailing_zeros n = trailing_zeros (n - 2 ^ (n.size - 2)) + 1 := by
  intro n hn1 hn2
  have n2 : 2 ≤ n.size := by
    have t1 : (2 : ℕ).size ≤ n.size := by exact size_le_size hn1
    have t2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
    exact le_of_eq_of_le (id (Eq.symm t2)) t1
  have t1 : trailing_zeros n = n.size - 1 := by
    rewrite (occs := .pos [1]) [hn2]
    exact trailing_zeros_of_envelope (n.size - 1)
  have t2 : n - 2 ^ (n.size - 2) = 2 ^ (n.size - 2) := by
    rewrite (occs := .pos [1]) [hn2]
    refine Nat.sub_eq_of_eq_add ?_
    rw [←mul_two]
    have : 2 ^ (n.size - 2) * 2 = 2 ^ (n.size - 2 + 1) := by exact rfl
    simp [this]
    exact (Nat.sub_eq_iff_eq_add n2).mp rfl
  simp [t1, t2]
  have : trailing_zeros (2 ^ (n.size - 2)) = n.size - 2 := by
    exact trailing_zeros_of_envelope (n.size - 2)
  simp [this]
  exact (Nat.sub_eq_iff_eq_add n2).mp rfl

/--
The number of trailing zeros in 2^n equals n.
-/
theorem trailing_zeros_prop3 : ∀ n : ℕ, trailing_zeros (2 ^ n) = n := by
  intro n
  rw [trailing_zeros.eq_def]
  split
  · expose_names
    have : ¬2 ^ n = 0 := by exact NeZero.ne (2 ^ n)
    exact absurd heq this
  · expose_names
    split
    · expose_names
      rw [h]
      have t1 : (2 ^ ((2 ^ n).size - 1)).size = (2 ^ n).size - 1 + 1 := by
        exact size_of_pow2_eq_self_add_one ((2 ^ n).size - 1)
      simp [t1]
      have t2 : (2 ^ n).size = n + 1 := by exact size_of_pow2_eq_self_add_one n
      exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm t2)))
    · expose_names
      have t1 : (2 ^ n).size = n + 1 := by exact size_of_pow2_eq_self_add_one n
      simp [t1] at h

/--
The number of trailing zeros in 2^n - 1 is always 0.
-/
theorem trailing_zeros_prop4 : ∀ n : ℕ, trailing_zeros (2 ^ n - 1) = 0 := by
  intro n
  induction n with
  | zero => simp [trailing_zeros.eq_def]
  | succ n hn =>
    rw [trailing_zeros.eq_def]
    split
    · expose_names ; exact heq
    · expose_names
      split
      · expose_names
        have t1 : (2 ^ (n + 1) - 1).size = n + 1 := by
          refine size_sub ?_ ?_ ?_
          · exact zero_lt_succ n
          · exact one_pos
          · exact Nat.one_le_two_pow
        simp [t1] at h
        have zp : n = 0 ∨ ¬n = 0 := by exact Or.symm (ne_or_eq n 0)
        rcases zp with z|p
        · simp [z] at *
        · have even : 2 ∣ 2 ^ n := by exact Dvd.dvd.pow (by grind) p
          have odd : ¬2 ∣ 2 ^ (n + 1) := by
            simp [←h] at even
            refine two_dvd_ne_zero.mpr ?_
            have h' : 2 ^ (n + 1) = 2 ^ n + 1 := by grind
            simp [h']
            grind
          have even' : 2 ∣ 2 ^ (n + 1) := by exact Dvd.intro_left (Nat.pow 2 n) rfl
          exact absurd even' odd
      · expose_names
        simp
        have : 2 ^ (n + 1) - 1 - 2 ^ ((2 ^ (n + 1) - 1).size - 1) = 2 ^ n - 1 := by
          have t1 : (2 ^ (n + 1) - 1).size = n + 1 := by exact size_sub (by grind) (by grind) (by grind)
          simp [t1]
          have t2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by grind
          simp [t2]
          grind
        simp [this]
        exact hn

/--
Powers of 2 plus 1 cannot equal other powers of 2 (contradiction lemma).
-/
theorem parity_unmatch {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2 ^ a + 1 = 2 ^ b) : false := by
  have two_pow_a_is_even : 2 ∣ 2 ^ a := by exact dvd_pow_self 2 (ne_zero_of_lt ha)
  have even : 2 ∣ 2 ^ a + 1 := by
    simp [h]
    exact Nat.ne_zero_of_lt hb
  have odd : ¬2 ∣ 2 ^ a + 1 := by
    refine Odd.not_two_dvd_nat ?_
    · refine Even.add_one ?_
      · exact (even_iff_exists_two_nsmul (2 ^ a)).mpr two_pow_a_is_even
  exact absurd even odd

/--
The number of trailing zeros in 2^(n+1) + 1 is always 0.
TODO: no need to induction
-/
theorem trailing_zeros_prop5 : ∀ n : ℕ, trailing_zeros (2 ^ (n + 1) + 1) = 0 := by
  intro n
  induction n with
  | zero =>
    simp
    rw [trailing_zeros]
    simp [size, binaryRec]
    rw [trailing_zeros]
    simp [size]
  | succ n hn =>
    rw [trailing_zeros]
    split
    · expose_names
      simp at h
      have sub1 : 0 < n + 1 + 1 := by grind
      have sub2 : 0 < (2 ^ (n + 1 + 1) + 1).size - 1 := by
        have t1 : 2 ≤ n + 1 + 1 := by grind
        have t2 : 2 ^ 2 ≤ 2 ^ (n + 1 + 1) := by exact Nat.pow_le_pow_right (by grind) t1
        have t3 : 2 ^ 2 = 4 := by grind
        simp [t3] at t2
        have t4 : 4 + 1 ≤ 2 ^ (n + 1 + 1) + 1 := by exact add_le_add_right t2 1
        have t5 : (4 + 1).size ≤ (2 ^ (n + 1 + 1) + 1).size := by exact size_le_size t4
        simp at t5
        rewrite (occs := .pos [1]) [size] at t5
        simp [binaryRec] at t5
        have t6 : 2 ≤ (2 ^ (n + 1 + 1) + 1).size - 1 := by exact le_sub_one_of_lt t5
        exact zero_lt_of_lt t6
      have c := parity_unmatch sub1 sub2 h
      simp at c
    · simp
      have t1 : (2 ^ (n + 1 + 1) + 1).size = n + 1 + 1 + 1 := by
        refine size_add (by grind) ?_
        · have s1 : 2 ≤ n + 1 + 1 := by exact le_add_left 2 n
          have s2 : 2 ^ 2 ≤ 2 ^ (n + 1 + 1) := by exact Nat.pow_le_pow_right (by grind) s1
          simp at s2
          exact one_lt_two_pow' (n + 1)
      simp [t1]
      simp [trailing_zeros]

/--
For positive n not equal to 2^(n.size-1), trailing_zeros(n) = trailing_zeros(n - 2^(n.size-1)).
-/
theorem trailing_zeros_prop6 : ∀ n > 0,
    ¬n = 2 ^ (n.size - 1) → trailing_zeros n = trailing_zeros (n - 2 ^ (n.size - 1)) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn'
    rw [trailing_zeros.eq_def]
    split
    · contradiction
    · split
      · expose_names ; exact absurd h hn'
      · expose_names ; simp

/--
For k < 2^n and k ≠ 0, trailing_zeros(k + 2^n) = trailing_zeros(k).
-/
theorem trailing_zeros_prop7 : ∀ n : ℕ, ∀ k < 2 ^ n,
    ¬k = 0 → trailing_zeros (k + 2 ^ n) = trailing_zeros k := by
  intro n k
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k' h1
    rw [trailing_zeros.eq_def]
    split
    · expose_names
      have c : ¬k + 2 ^ n = 0 := by
        have : 0 < 2 ^ n := by exact Nat.two_pow_pos n
        exact NeZero.ne (k + 2 ^ n)
      exact absurd heq c
    · have zp : n = 0 ∨ 0 < n := by exact Nat.eq_zero_or_pos n
      rcases zp with z|p
      · simp [z] at *
        exact absurd k' h1
      · have n2 : (2 ^ n).size = n + 1 := by exact size_of_pow2_eq_self_add_one n
        have s1 : 2 ^ n + k < 2 ^ n + 2 ^ n := by exact add_lt_add_left k' (2 ^ n)
        rw [←mul_two] at s1
        have so : (2 ^ n + k).size = n + 1 := by
          have left : n + 1 ≤ (2 ^ n + k).size := by
            have : (2 ^ n).size ≤ (2 ^ n + k).size := by
              refine size_le_size ?_
              exact le_add_right (2 ^ n) k
            exact le_of_eq_of_le (id (Eq.symm n2)) this
          have right : (2 ^ n + k).size ≤ n + 1 := by
            exact pow2_is_minimum (n + 1) (2 ^ n + k) s1
          exact Eq.symm (le_antisymm left right)
        have eq_size : (2 ^ n + k).size = (2 ^ n).size := by
          refine size_add' (by grind) ?_
          · have s4 : (2 ^ n + k).size = (2 ^ n).size := by simp [so, n2]
            simp [s4]
        split
        · expose_names
          have t1 : 2 ^ n < k + 2 ^ n := by
            refine Nat.lt_add_of_pos_left ?_
            exact zero_lt_of_ne_zero h1
          have t2 : 2 ^ n = 2 ^ ((2 ^ n).size - 1) := by
            have : (2 ^ n).size = n + 1 := by exact size_of_pow2_eq_self_add_one n
            simp [this]
          rewrite (occs := .pos [1]) [t2] at t1
          clear t2
          simp [←eq_size] at t1
          rewrite (occs := .pos [1]) [add_comm] at t1
          have c : ¬k + 2 ^ n = 2 ^ ((k + 2 ^ n).size - 1) := by exact Nat.ne_of_lt' t1
          exact absurd h c
        · expose_names
          simp
          have : k + 2 ^ n - 2 ^ ((k + 2 ^ n).size - 1) = k := by
            have t1 : (k + 2 ^ n).size = n + 1 := by
              have : (k + 2 ^ n).size = (2 ^ n).size := by
                rw [add_comm]
                exact eq_size
              simp only [this, n2]
            simp [t1]
          exact congrArg trailing_zeros this

/- #eval List.range 6 |>.map (fun n' ↦
    let o := n'
    let n := n' + 2
    ((∑ i ∈ range (o - 1), (trailing_zeros (2 ^ n + i + 1) + 1) + 1),
    (∑ i ∈ range (o - 1), (trailing_zeros (        i + 1) + 1) + 1))) -/

/--
For k ≤ 2^n, the sum of (trailing_zeros(2^n + i + 1) + 1) over i ∈ [0, k-2] equals
the sum of (trailing_zeros(i + 1) + 1) over the same range.
-/
theorem trailing_zeros_prop8 : ∀ n : ℕ, ∀ k ≤ 2 ^ n,
    ∑ i ∈ range (k - 1), (trailing_zeros (2 ^ n + i + 1) + 1)
    = ∑ i ∈ range (k - 1), (trailing_zeros (      i + 1) + 1) := by
  intro n k hk
  let f1 := (fun i ↦ if h : i < 2 ^ n then trailing_zeros (i + 2 ^ n) else 0)
  have f1_def : f1 = value_of% f1 := by exact rfl
  have f1eq : f1 = (fun i ↦
      if h : i < 2 ^ n
      then if h' : i == 0 then trailing_zeros (2 ^ n) else trailing_zeros i
      else 0) := by
    simp [f1_def]
    ext x
    split
    · expose_names
      split
      · expose_names ; simp [h_1]
      · expose_names ; refine trailing_zeros_prop7 n x h h_1
    · expose_names ; simp at h ; exact rfl
  have t1 :
     (∑ x ∈ range (k - 1), (trailing_zeros (2 ^ n + x + 1) + 1)) =
     (∑ x ∈ range (k - 1), (f1             (        x + 1) + 1)) := by
    simp [f1_def]
    refine sum_congr rfl ?_
    · intro y hy
      split
      · expose_names
        have : 2 ^ n + y + 1 = y + 1 + 2 ^ n := by grind
        simp [this]
      · expose_names
        have t1 : y     < k - 1 := by exact List.mem_range.mp hy
        have t2 : y + 1 < k     := by exact add_lt_of_lt_sub t1
        have t3 : y + 1 < 2 ^ n := by exact lt_of_lt_of_le t2 hk
        exact absurd t3 h
  simp [t1]
  clear t1
  let f2 := (fun i ↦ if h : (i + 1) < 2 ^ n then trailing_zeros ((i + 1) + 2 ^ n) else 0)
  have f2_def : f2 = value_of% f2 := by exact rfl
  have t2 :
      (∑ i ∈ range (k - 1), (f1 (i + 1) + 1)) =
      (∑ i ∈ range (k - 1), (f2  i      + 1)) := by
    exact rfl
  simp [t2]
  let f3 := (fun i ↦ if h : i +1 < 2 ^ n then trailing_zeros (i + 1) else 0)
  have f3_def : f3 = value_of% f3 := by exact rfl
  have f2eqf3 : f2 = f3 := by
    simp [f2_def, f3_def]
    ext i
    split
    · expose_names ; refine trailing_zeros_prop7 n (i + 1) h (by grind)
    · exact rfl
  simp [f2eqf3]
  have t3 :
     (∑ i ∈ range (k - 1), (trailing_zeros (i + 1) + 1)) =
     (∑ i ∈ range (k - 1), (f3              i + 1)) := by
    simp [f3_def]
    refine sum_congr rfl ?_
    · intro y hy
      split
      · expose_names ; exact rfl
      · expose_names
        have t1 : y     < k - 1 := by exact List.mem_range.mp hy
        have t2 : y + 1 < k     := by exact add_lt_of_lt_sub t1
        have t3 : y + 1 < 2 ^ n := by exact lt_of_lt_of_le t2 hk
        exact absurd t3 h
  simp [t3]

/--
  For any positive natural number `n`, appending a `1` bit to the front of the binary
  representation of `n` (i.e. going from `2 * n` to `2 * n + 1`) does not change the
  length of the bit-list, and hence does not change the `size` (the bit-length)
  of the corresponding natural number.

  In binary terms, for `n > 0` we have
  `(2 * n).bits = false :: n.bits` and `(2 * n + 1).bits = true :: n.bits`,
  so both bit-lists have the same length `n.bits.length + 1`. Note that the
  assumption `n > 0` is necessary: for `n = 0` we have `0.size = 0` but `1.size = 1`.
  -/
theorem size_of_even_add_one_eq_size_of_self : ∀ n > 0,
    (2 * n).size = (2 * n + 1).size := by
  intro n h
  let bv := n.bits
  have hbv : bv = value_of% bv := by exact rfl
  have two0 : (2 * n).bits = false :: bv := by
    exact bits_of_double_eq_cons_false_and_bits n h
  have two1 : (2 * n + 1).bits = true :: bv := by exact bit1_bits n
  have t1 : (2 * n).bits.length = (2 * n + 1).bits.length := by
    simp only [two0, two1]
    exact rfl
  simp only [bitslength_eq_size] at t1
  exact t1

/--
If `n ≥ 2` and `n = 2 ^ (n.size - 1)` (so `n` is a power of two), then
for every `n' < n` we have `trailing_zeros n' < trailing_zeros n`.

In other words, among all natural numbers strictly less than a positive power of two,
that power of two itself has the maximum possible number of trailing zero bits.

This lemma is useful for measure-based arguments: when splitting an interval at the
largest power-of-two boundary below an upper limit, the `trailing_zeros` measure strictly
drops on the left part.
-/
theorem trailing_zeros_of_pow2_is_max : ∀ n ≥ 2, n = 2 ^ (n.size - 1) →
    ∀ n' < n, trailing_zeros n' < trailing_zeros n := by
  intro n hn
  have nsize2 : n.size ≥ 2 := by
    have t1 : (2 : ℕ).size ≤ n.size := by exact size_le_size hn
    have t2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
    simp [t2] at t1
    exact t1
  induction n using Nat.strong_induction_on with
  | h n hn' =>
    intro n₁ n₂ hn'2
    let m := 2 ^ (n.size - 2)
    have hm : m = value_of% m := by exact rfl
    have cases : n = 2 ∨ n > 2 := by
      refine Nat.eq_or_lt_of_not_lt ?_
      · simp
        exact hn
    rcases cases with n_eq_two|n_gt_two
    · simp [n_eq_two] at *
      have cases' : n₂ = 0 ∨ n₂ = 1 := by
        refine le_one_iff_eq_zero_or_eq_one.mp ?_
        · exact le_of_lt_succ hn'2
      rcases cases' with n₂|n₂
      <;> { simp [n₂, trailing_zeros] }
    · -- 前半分と後ろ半分
      have sub1 : m < n := by
        refine le_if_le_size ?_
        · simp [hm]
          have : (2 ^ (n.size - 2)).size = n.size - 2 + 1 := by
            exact size_of_pow2_eq_self_add_one (n.size - 2)
          simp [this]
          grind
      have n4 : n ≥ 4 := by
        have n_3_4 : n = 3 ∨ n > 3 := by
          exact LE.le.eq_or_lt' n_gt_two
        rcases n_3_4 with n_eq_3|n_gt_3
        · simp [n_eq_3] at *
        · exact n_gt_3
      have n4size : n.size ≥ 3 := by
        have t1 : n.size ≥ (4 : ℕ).size := by exact size_le_size n4
        have t2 : (4 : ℕ).size = 3 := by simp [size, binaryRec]
        simp [t2] at t1
        exact t1
      have sub2 : m ≥ 2 := by
        refine Nat.le_self_pow ?_ 2
        · exact Nat.sub_ne_zero_iff_lt.mpr n4size
      have sub3 : m.size ≥ 2 := by
        have t1 : m.size ≥ (2 : ℕ).size := by exact size_le_size sub2
        have t2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
        simp [t2] at t1
        exact t1
      have sub4 : m = 2 ^ (m.size - 1) := by
        simp [hm]
        have t1 : (2 ^ (n.size - 2)).size = n.size - 2 + 1 := by
          exact size_of_pow2_eq_self_add_one (n.size - 2)
        simp [t1]
      have divide_and_conquer : n₂ < m ∨ n₂ ≥ m := by exact Nat.lt_or_ge n₂ m
      have trailing_zeros_m : trailing_zeros m = n.size - 2 := by
        simp [hm]
        exact trailing_zeros_prop3 (n.size - 2)
      have trailing_zeros_n : trailing_zeros n = n.size - 1 := by
        rewrite (occs := .pos [1]) [n₁]
        exact trailing_zeros_prop3 (n.size - 1)
      rcases divide_and_conquer with first_part|others
      · have trans1 : trailing_zeros m < trailing_zeros n := by
          simp [trailing_zeros_m, trailing_zeros_n]
          exact sub_succ_lt_self n.size 1 nsize2
        have g := hn' m sub1 sub2 sub3 sub4 n₂ first_part
        have trans2 : trailing_zeros n₂ < trailing_zeros m := by exact g
        exact Nat.lt_trans g trans1
      · have split_again : n₂ = m ∨ n₂ > m := by exact LE.le.eq_or_lt' others
        rcases split_again with n₂_eq_m|n₂_gt_m
        · simp [n₂_eq_m] at *
          simp [trailing_zeros_m, trailing_zeros_n]
          exact sub_succ_lt_self n.size 1 nsize2
        · -- slide to the left
          let n₂' := n₂ - m
          have n₂_def : n₂' = value_of% n₂' := by exact rfl
          have n₂_def' : n₂ = 2 ^ (m.size - 1) + n₂' := by
            simp [←sub4]
            exact Eq.symm (add_sub_of_le others)
          have n₂'_range : n₂' < m := by
            have t1 : m + m = n := by
              simp [hm]
              calc
                2 ^ (n.size - 2) + 2 ^ (n.size - 2) = 2 ^ (n.size - 2) * 2 := by
                  exact Eq.symm (Nat.mul_two (2 ^ (n.size - 2)))
                _ = 2 ^ (n.size - 2 + 1) := by exact rfl
                _ = 2 ^ (n.size - 1) := by
                  have : n.size - 2 + 1 = n.size - 1 := by
                    refine Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) ?_)
                    exact (Nat.sub_eq_iff_eq_add nsize2).mp rfl
                  simp [this]
                _ = n := by simp [←n₁]
            have t2 : n₂ = n₂' + m := by exact (Nat.sub_eq_iff_eq_add others).mp n₂_def
            simp [←t1, t2] at hn'2
            exact hn'2
          have shift_left : trailing_zeros n₂ = trailing_zeros n₂' := by
            rewrite [n₂_def', add_comm]
            refine trailing_zeros_prop7 (m.size - 1) n₂' ?_ ?_
            · simp [←sub4] ; exact n₂'_range
            · by_contra h
              simp [h] at *
              have c : n₂ = m := by grind
              have : ¬n₂ = m := by exact Nat.ne_of_lt' n₂_gt_m
              exact absurd c this
          simp [shift_left]
          have g := hn' m sub1 sub2 sub3 sub4 n₂' n₂'_range
          have g' : trailing_zeros m < trailing_zeros n := by
            simp [trailing_zeros_m, trailing_zeros_n]
            exact sub_succ_lt_self n.size 1 nsize2
          exact Nat.lt_trans g g'

/--
If incrementing n increases the size by 1, then n + 1 must be a power of 2.
This is the converse of size_of_pow2_eq_size_of_envelope_add_1, showing that
size increases happen if and only if we reach a power of 2.
-/
theorem increase_size_at_pow2 {n : ℕ} :
    (n + 1).size = n.size + 1 → n + 1 = 2 ^ ((n + 1).size - 1) := by
  intro eq
  by_contra ne_pow2
  by_cases n_eq_0 : n = 0
  · simp [n_eq_0] at ne_pow2
  · replace n_eq_0 : n > 0 := by exact zero_lt_of_ne_zero n_eq_0
    replace n_eq_0 : n ≥ 1 := by exact n_eq_0
    by_cases n_eq_1 : n = 1
    · simp [n_eq_1, size, binaryRec] at ne_pow2
    · have n_ge_2 : n ≥ 2 := by
        refine (two_le_iff n).mpr ?_
        · constructor
          · exact Nat.ne_zero_of_lt n_eq_0
          · exact n_eq_1
      clear n_eq_0 n_eq_1
      have s1 : n + 1 < 2 ^ n.size := by
        simp [eq] at ne_pow2
        have : n < 2 ^ n.size := by exact lt_size_self n
        replace : n + 1 ≤ 2 ^ n.size := by exact this
        replace : n + 1 < 2 ^ n.size ∨ n + 1 = 2 ^ n.size := by
          exact Or.symm (Nat.eq_or_lt_of_le this)
        rcases this with lt|eq
        · exact lt
        · exact absurd eq ne_pow2
      have s2 : (n + 1).size ≤ n.size := by
        exact pow2_is_minimum n.size (n + 1) s1
      replace eq : (n + 1).size > n.size := by grind
      replace eq : ¬(n + 1).size ≤ n.size := by exact Nat.not_le_of_lt eq
      exact absurd s2 eq

/--
The size of `n + 1` increases by 1 if and only if `n + 1` is a power of 2.
This characterizes exactly when the bit size increases.
-/
theorem increase_size_iff_pow2 {n : ℕ} :
    (n + 1).size = n.size + 1 ↔ n + 1 = 2 ^ ((n + 1).size - 1) := by
  constructor
  · exact increase_size_at_pow2
  · intro h
    exact size_of_pow2_eq_size_of_envelope_add_1' (zero_lt_succ n) h

/--
The size of `n + 1` stays the same as `n.size` if and only if `n + 1` is not a power of 2.
This is the contrapositive of `increase_size_iff_pow2`.
-/
theorem same_size_iff_not_pow2 {n : ℕ} :
    ¬n + 1 = 2 ^ ((n + 1).size - 1) ↔ (n + 1).size = n.size := by
  have it {a b : Prop} : (a → b) → (¬b → ¬a) := by exact fun a_1 a_2 a ↦ a_2 (a_1 a)
  constructor
  · intro p
    have : (n + 1).size = n.size + 1 → n + 1 = 2 ^ ((n + 1).size - 1) := by
      exact fun a ↦ increase_size_at_pow2 a
    replace this := it this p
    have cases : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := by exact size_limit n
    rcases cases with q|q
    · exact q
    · exact absurd q this
  · intro p
    have cases : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := by exact size_limit n
    rcases cases with q|q
    · replace q : ¬(n + 1).size = n.size + 1 := by simp [p]
      have : n + 1 = 2 ^ ((n + 1).size - 1) → (n + 1).size = n.size + 1 := by
        exact fun a ↦ increase_size_iff_pow2.mpr a
      replace this := it this q
      exact this
    · simp [q] at p

/--
For n ≥ 4, if `n + 2` is a power of 2, then its size is one more than `n.size`.
This is a variant of `increase_size_iff_pow2` specialized for the case of adding 2.
-/
theorem increase_size_iff_pow2' {n : ℕ} (h : n ≥ 4) :
    n + 2 = 2 ^ ((n + 2).size - 1) → (n + 2).size = n.size + 1 := by
  intro h'
  have s1 : (n + 1).size + 1 = (n + 2).size := by
    exact Eq.symm ((fun {n} ↦ increase_size_iff_pow2.mpr) h')
  have s2 : (n + 1).size = n.size := by
    refine same_size_iff_not_pow2.mp ?_
    · by_contra ch
      have : n + 2 = n + 1 + 1 := by exact rfl
      rewrite (occs := .pos [1]) [this] at h'
      rw [ch] at h'
      have n1size_gt_3 : (n + 1).size ≥ 3 := by
        have s1 : (n + 1).size ≥ (4 + 1).size := by
          exact size_le_size (Nat.add_le_add_right h 1)
        have s2 : (4 + 1).size = 3 := by simp [size, binaryRec]
        simp [s2] at s1
        exact s1
      have n2size_gt_3 : (n + 2).size ≥ 3 := by
        have s1 : (n + 2).size ≥ (4 + 2).size := by
          exact size_le_size (Nat.add_le_add_right h 2)
        have s2 : (4 + 2).size = 3 := by simp [size, binaryRec]
        simp [s2] at s1
        exact s1
      have even : Even (2 ^ ((n + 2).size - 1)) := by
        refine (even_pow' ?_).mpr ?_
        · refine Nat.sub_ne_zero_iff_lt.mpr ?_
          · exact lt_of_add_left_lt n2size_gt_3 
        · exact even_iff.mpr rfl
      have odd : Odd (2 ^ ((n + 1).size - 1) + 1) := by
        refine Even.add_one ?_
        · refine (even_pow' ?_).mpr ?_
          · refine Nat.sub_ne_zero_iff_lt.mpr ?_
            · exact lt_of_add_left_lt n1size_gt_3
          · exact even_iff.mpr rfl
      simp [h'] at odd
      replace odd : ¬Even (2 ^ ((n + 2).size - 1)) := by exact not_even_iff_odd.mpr odd
      exact absurd even odd
  simp [←s2, s1]

