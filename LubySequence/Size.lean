module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.Group.Defs

open Finset Nat

/--
The size (bit length) of the natural number 2 is 2.
-/
@[simp]
public theorem size2_eq_2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]

/--
The size (bit length) of 3 is 2.
-/
@[simp]
public theorem size3_eq_2 : (3 : ℕ).size = 2 := by simp [size, binaryRec]

/--
The size (bit length) of 4 is 3.
-/
@[simp]
public theorem size4_eq_3 : (4 : ℕ).size = 3 := by simp [size, binaryRec]

/--
For any natural number n ≥ 2, its size (bit length) is at least 2.
-/
@[simp]
public theorem size2_ge_2 {n : ℕ} (h : n ≥ 2) : n.size ≥ 2 := by
  have s1 : n.size ≥ (2 : ℕ).size := by exact size_le_size h
  simp at s1
  exact s1

/--
For any natural number n ≥ 2, the size of n + 2 is at least 3.
-/
@[simp]
public theorem size2_add_2_ge_2 {n : ℕ} (h : n ≥ 2) : (n + 2).size ≥ 3 := by
  have s1 : n + 2 ≥ 2 + 2 := by exact Nat.add_le_add_right h 2
  have s2 : (n + 2).size ≥ (2 + 2).size := by exact size_le_size s1
  simp at s2
  exact s2

/--
For any natural number n ≥ 4, the size of n is at least 3.
-/
@[simp]
public theorem size4_add_0_ge_2 {n : ℕ} (h : n ≥ 4) : n.size ≥ 3 := by
  have s1 : n.size ≥ (4 : ℕ).size := by exact size_le_size h
  simp at s1
  exact s1

/--
Every natural number is strictly less than 2 raised to the power of its size plus one.
-/
public theorem self_ne_pow_two_succ_of_size (n : ℕ) : n < 2 ^ n.size.succ := by exact size_le.mp (by grind)

/--
The length of the bit representation equals the size of a natural number.
-/
public theorem bitslength_eq_size (n : ℕ) : n.bits.length = n.size := by exact size_eq_bits_len n

/--
The bit representation of `2 * n` is false (0) prepended to the bit representation of n.
-/
public theorem bits_of_double_eq_cons_false_and_bits (n : ℕ) (h : n > 0) :
    ((2 : ℕ) * n).bits = false :: n.bits := by
  have : n ≠ 0 := by exact ne_zero_of_lt h
  exact bit0_bits n this

/--
The size of `2 * n` is one more than the size of n (for positive n).
-/
public theorem size_of_double_eq_self_add_one (n : ℕ) (h : n > 0) : ((2 : ℕ) * n).size = n.size + 1 := by
  have h : (2 * n).bits = false :: n.bits := by
    exact bits_of_double_eq_cons_false_and_bits n h
  have t1 : (2 * n).bits.length = (false :: n.bits).length := by
    exact congrArg List.length h
  have t2 : (false :: n.bits).length = n.bits.length + 1 := by
    exact rfl
  simp [t2, bitslength_eq_size] at t1
  exact t1

/--
For `n ≥ 2` and `k < 2 ^ n`, adding k to `2 ^ n` does not change the bit size.
In other words, `(2 ^ n + k).size = (2 ^ n).size` when k is strictly less than `2 ^ n`.
-/
public theorem size_of_pow2 {k n : ℕ} (h2 : k < 2 ^ n) :
    (2 ^ n + k).size = ((2 : ℕ) ^ n).size := by
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
The bit representation of `2 * n + 1` is true (1) prepended to the bit representation of n.
-/
example (n : ℕ) : (2 * n + 1).bits = true :: n.bits := by
  exact bit1_bits n

/--
The size of `n * 2` equals `n.size + 1` (for positive n).
-/
theorem size_of_two_mul_eq_aize_add_one (n : ℕ) (h : n > 0) :
    n.size + 1 = (n * 2).size := by
  simp [←size_eq_bits_len, mul_comm n 2, bits_of_double_eq_cons_false_and_bits n h]

/--
If `2 * a < b`, then the size of a is less than the size of b.
-/
public theorem size_lt {a b : ℕ} (h : 0 < a) : (2 : ℕ) * a < b → a.size < b.size := by
  intro hg
  have s1 : (2 * a).bits = false :: a.bits := bit0_bits a (by grind)
  have s2 : (false :: a.bits).length = 1 + a.bits.length := succ_eq_one_add a.bits.length
  have s3 :(2 * a).bits.length = 1 + a.bits.length := by simp only [s1, s2]
  simp [bitslength_eq_size] at s3
  have stricten (a b c : ℕ) (h : 0 < b) : (a + b = c) → (a < c) := by
    intro hh
    obtain t|f : a < c ∨ a = c := Or.symm (eq_or_lt_of_le (@le.intro a c b hh))
    · expose_names ; exact t
    · expose_names
      simp [f] at hh
      have : ¬b = 0 := ne_zero_of_lt h
      exact absurd hh this
  have tr1 : a.size < (2 * a).size := stricten a.size 1 (2 * a).size (by grind) (by grind)
  replace hg : 2 * a ≤ b := le_of_succ_le hg
  have tr2 : (2 * a).size ≤ b.size := size_le_size hg
  exact lt_of_lt_of_le tr1 tr2

/--
For positive n, `2 ^ n.size ≤ 2 * n`.
-/
public theorem pow_two_of_size_le_self {n : ℕ} (h : 0 < n) : 2 ^ n.size ≤ (2 : ℕ) * n := by
  refine lt_size.mp ?_
  have s1 : (2 * n).bits = false :: n.bits := bit0_bits n (by grind)
  have s2 : (false :: n.bits).length = 1 + n.bits.length := succ_eq_one_add n.bits.length
  have s3 : (2 * n).bits.length = 1 + n.bits.length := by simp only [s1, s2]
  simp [bitslength_eq_size] at s3
  simp [s3]

/--
The bit representation length of `2 ^ n` equals `n + 1`.
-/
theorem bitslength_of_pow2_eq_self_add_one (n : ℕ) : (2 ^ n).bits.length = n + 1 := by
  induction n with
  | zero => simp
  | succ n hn =>
    have p : 0 < 2 ^ n := Nat.two_pow_pos n
    let v := (2 ^ n).bits
    have vp : v = value_of% v := rfl
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by grind
    simp [this]
    exact hn

/--
The size of `2 ^ n` equals `n + 1`.
-/
public theorem size_of_pow2_eq_self_add_one (n : ℕ) : ((2 : ℕ) ^ n).size = n + 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_of_pow2_eq_self_add_one n

/--
The bit representation of `2 ^ n` consists of n false bits followed by one true bit.
-/
theorem pow2_bit {n : ℕ} : (2 ^ n).bits = List.iterate (·) false n ++ [true] := by
  induction n with
  | zero => simp
  | succ n hn =>
    have s1 : 2 ^ (n + 1) = 2 * (2 ^ n) := pow_succ'
    simp [s1]
    exact hn

/--
The bit representation of `2 ^ n - 1` consists of n true bits.
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
          · have : 0 < 2 ^ n := by exact Nat.two_pow_pos n
            grind
        _ = 2 * (2 ^ n - 1) + 1 := by rw [add_comm]
    simp [s1]
    exact hn

/--
Deprecated: Use `size_add` instead.
For `0 < k < 2 ^ n`, the size of `2 ^ n + k` equals `n + 1`.
-/
public theorem size_add {n k : ℕ} (ha : 0 < k) (hb : k < 2 ^ n) : (2 ^ n + k).size = n + 1 := by
  simp [←bitslength_eq_size]
  have p1 : (2 ^ n).bits.length ≤ (2 ^ n + k).bits.length := by
    have : (2 ^ n).size ≤ (2 ^ n + k).size := size_le_size (le_add_right (2 ^ n) k)
    simp only [←bitslength_eq_size] at this
    exact this
  have p1' : n + 1 ≤ (2 ^ n + k).bits.length := by
    have : (2 ^ n).bits.length = n + 1 := bitslength_of_pow2_eq_self_add_one n
    simp [this] at p1
    exact p1
  have p2 : 2 ^ n + k ≤ 2 ^ (n + 1) - 1 := by
    have : 2 ^ (n + 1) = 2 * 2 ^ n := pow_succ'
    simp [this]
    replace : 2 * 2 ^ n = 2 ^ n + 2 ^ n := two_mul (2 ^ n)
    simp [this]
    have : 2 ^ n + 2 ^ n - 1 = 2 ^ n - 1 + 2 ^ n := by
      have : 2 ^ n + 2 ^ n - 1 = 2 ^ n + (2 ^ n - 1) := Nat.add_sub_assoc (by grind) (2 ^ n)
      rw [add_comm _ (2 ^ n - 1)] at this
      exact this
    simp [this]
    rw [add_comm]
    exact Nat.add_le_add_iff_right.mpr (le_sub_one_of_lt hb)
  have p2' : (2 ^ n + k).bits.length ≤ n + 1 := by
    have s1 : (2 ^ n + k).bits.length ≤ (2 ^ (n + 1) - 1).bits.length := by
      have : (2 ^ n + k).size ≤ (2 ^ (n + 1) - 1).size := size_le_size p2
      simp [←bitslength_eq_size] at this
      exact this
    have s2 : (2 ^ (n + 1) - 1).bits.length = n + 1 := by
      have : (2 ^ (n + 1) - 1).bits = List.iterate (·) true (n + 1) := pow2_sub_one
      simp [this]
    simp [s2] at s1
    exact s1
  exact le_antisymm p2' p1'

/--
If adding k to n doesn't increase the size beyond n.size, then the size stays the same.
-/
public theorem size_add' {n k : ℕ} (ha : 0 < k) (hb : (n + k).size < n.size + 1) : (n + k).size = n.size := by
  have t1 : n < n + k := by exact Nat.lt_add_of_pos_right ha
  have t2 : n.size ≤ (n + k).size := size_le_size (by grind)
  obtain l|e : n.size < (n + k).size ∨ n.size = (n + k).size := Or.symm (eq_or_lt_of_le t2)
  · have l' : ¬(n + k).size < n.size + 1 := not_lt.mpr l
    exact absurd hb l'
  · exact id (Eq.symm e)

/--
For `n > 0` and `0 < k ≤ 2 ^ (n - 1)`, the size of `2 ^ n - k` equals n.
-/
public theorem size_sub {n k : ℕ} (h : 0 < n) (ha : 0 < k) (hb : k ≤ 2 ^ (n - 1)) : (2 ^ n - k).size = n := by
  have p1 : 0 < n := by
    have p : 1 ≤ n := by exact h
    have t1 : (1 : ℕ).size ≤ n := by
      have : (1 : ℕ).size ≤ n.size := size_le_size h
      simp
      exact p
    simp at t1
    have t2 : 0 < 1 := by grind
    grind
  have r1 : 2 ^ n - 1 ≥ 2 ^ n - k := by grind
  have e1 : (2 ^ n - 1).bits.length = n := by simp [pow2_sub_one]
  simp [bitslength_eq_size] at e1
  have t1 : (2 ^ n - k).size ≤ (2 ^ n - 1).size := by
    have : 2 ^ n - k ≤ 2 ^ n - 1 := r1
    exact size_le_size r1
  simp [e1] at t1
  clear e1 r1
  have t2 : n ≤ (2 ^ n - k).size := by
    have r2 : 2 ^ n - 2 ^ (n - 1) ≤ 2 ^ n - k := Nat.sub_le_sub_left hb (2 ^ n)
    replace r2 : (2 ^ n - 2 ^ (n - 1)).size ≤ (2 ^ n - k).size := size_le_size r2
    have e2 : 2 ^ n - 2 ^ (n - 1) = 2 ^ (n - 1) := by
      have step1 : 2 ^ n = 2 * 2 ^ (n - 1) := Eq.symm (mul_pow_sub_one (by grind) 2)
      simp [step1]
      have step2 : 2 * 2 ^ (n - 1) - 2 ^ (n - 1) = 2 ^ (n - 1) := by
        calc
          2 * 2 ^ (n - 1) - 2 ^ (n - 1) = 2 * 2 ^ (n - 1) - 1 * 2 ^ (n - 1) := by
            have : 2 ^ (n - 1) = 1 * 2 ^ (n - 1) := Eq.symm (one_mul (2 ^ (n - 1)))
            rewrite (occs := .pos [2]) [this]
            exact rfl
          _ = (2 - 1) * 2 ^ (n - 1) := Eq.symm (Nat.sub_mul 2 1 (2 ^ (n - 1)))
          _ = 2 ^ (n - 1) := (mul_eq_right (Ne.symm (NeZero.ne' (2 ^ (n - 1))))).mpr rfl
      simp [step2]
    replace e2 : (2 ^ n - 2 ^ (n - 1)).size = (2 ^ (n - 1)).size := by
      have : (2 ^ n - 2 ^ (n - 1)).size = (2 ^ (n - 1)).size := congrArg size e2
      exact this
    simp [e2] at r2
    replace e2 : (2 ^ (n - 1)).size = n := by
      have step1 : (2 ^ (n - 1)).bits.length = n - 1 + 1 := bitslength_of_pow2_eq_self_add_one (n - 1)
      have step2 : n - 1 + 1 = n := Nat.sub_add_cancel p1
      simp [step2, bitslength_eq_size] at step1
      exact step1
    simp [e2] at r2
    exact r2
  exact le_antisymm t1 t2

/--
If a has a strictly smaller size than b, then a < b.
-/
public theorem le_if_le_size {a b : ℕ} : a.size < b.size → a < b := by
  intro h1
  by_contra h2
  simp at h2
  have c1 : b.size ≤ a.size := by exact size_le_size h2
  have c2 : ¬a.size < b.size := by exact not_lt.mpr c1
  exact absurd h1 c2

/--
For any n, the size of `n + 1` is either equal to `n.size` or `n.size + 1`.
-/
public theorem size_limit (n : ℕ) : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := by
  by_cases h : n = 0
  · simp [h]
  · replace h : n > 0 := zero_lt_of_ne_zero h
    have s1 : n.size ≤ (n + 1).size := size_le_size (le_add_right n 1)
    have s2 : (n + 1).size ≤ n.size + 1 := by
      have t1 : (2 * n).size = n.size + 1 := size_of_double_eq_self_add_one n h
      have t2 : n + 1 ≤ 2 * n := add_one_le_two_mul h
      have t2' : (n + 1).size ≤ (2 * n).size := size_le_size t2
      simp [t1] at t2'
      exact t2'
    by_contra h'
    push_neg at h'
    obtain ⟨a, b⟩ := h'
    have c1 : n.size < (n + 1).size := lt_of_le_of_ne s1 (id (Ne.symm a))
    have c2 : (n + 1).size < n.size + 1 := lt_of_le_of_ne s2 b
    replace c2 : (n + 1).size ≤ n.size := le_of_lt_succ c2
    replace c2 : ¬(n + 1).size > n.size := not_lt.mpr c2
    exact absurd c1 c2

/--
Every natural number less than `2 ^ k` has size at most k.
-/
public theorem pow2_is_minimum (k : ℕ) : ∀ n < ((2 : ℕ) ^ k) , n.size ≤ k := by
  intro n hn
  have t1 : n.size ≤ (2 ^ k).size := size_le_size (le_of_succ_le hn)
  have t2 : (2 ^ k).size = k + 1 := size_of_pow2_eq_self_add_one k
  simp [t2] at t1
  exact size_le.mpr hn

/--
If n is an "envelope" (`n = 2 ^ n.size - 1`), then incrementing n increases the size by exactly 1.
This characterizes when the bit size increases: it happens precisely at powers of 2 minus 1.
-/
theorem size_of_pow2_eq_size_of_envelope_add_1 {n : ℕ} :
    n = 2 ^ n.size - 1 → (n + 1).size = n.size + 1 := by
  intro n_is_envelope
  rw (occs := .pos [1]) [n_is_envelope]
  have : 2 ^ n.size - 1 + 1 = 2 ^ n.size := Nat.sub_add_cancel (Nat.one_le_two_pow)
  simp [this]
  replace : (2 ^ n.size).size = n.size + 1 := size_of_pow2_eq_self_add_one n.size
  simp [this]

/--
For positive n equal to `2 ^ (n.size - 1)`, the size of n is one more than the size of `n - 1`.
This is a variant characterization showing when a number is exactly a power of 2.
-/
public theorem size_of_pow2_eq_size_of_envelope_add_1' {n : ℕ} (h : n > 0) :
    n = 2 ^ (n.size - 1) → n.size = (n - 1).size + 1 := by
  intro n_is_envelope
  have n_mp : n - 1 + 1 = n := Nat.sub_add_cancel h
  have nsize_mp : n.size - 1 + 1 = n.size := by
    refine Nat.sub_add_cancel ?_
    · replace h : n ≥ 1 := h
      exact one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (size_pos.mpr h))
  obtain eq|gt : (n - 1 + 1).size = (n - 1).size ∨ (n - 1 + 1).size = (n - 1).size + 1 := size_limit (n - 1)
  · have s1 : (n - 1).size < n.size := by
      have s1 : n - 1 < 2 ^ (n.size - 1) := by
        rw [←n_is_envelope]
        exact sub_one_lt_of_lt h
      have : (n - 1).size ≤ n.size - 1 := pow2_is_minimum (n.size - 1) (n - 1) s1
      replace : (n - 1).size < n.size - 1 + 1 := Order.lt_add_one_iff.mpr this
      simp [nsize_mp] at this
      exact this
    simp [n_mp] at eq
    simp [eq] at s1
  · simp [n_mp] at gt
    exact gt

/--
For `n ≥ 1`, n is at least `2 ^ (n.size - 1)`.
-/
public theorem n_ge_subenvelope {n: ℕ} (h : 1 ≤ n) : n ≥ 2 ^ (n.size - 1) := by
  obtain t|f : 1 = n ∨ 1 < n := by exact eq_or_lt_of_le h
  · simp [←t]
  · have n2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
    have h1 : 2 ≤ n := f
    have h2 : 2 ≤ n.size := by
      have t1 : (2 : ℕ).size ≤ n.size := size_le_size f
      simp [n2] at t1
      exact t1
    have : n > 2 ^ (n.size - 1) - 1 := by
      have : n.size > (2 ^ (n.size - 1) - 1).size := by
        have : (2 ^ (n.size - 1) - 1).size = n.size - 1 := by
          refine size_sub ?_ (by grind) ?_
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
If incrementing n increases the size by 1, then n + 1 must be a power of 2.
This is the converse of size_of_pow2_eq_size_of_envelope_add_1, showing that
size increases happen if and only if we reach a power of 2.
-/
public theorem increase_n1size_at_pow2 {n : ℕ} : (n + 1).size = n.size + 1 → n + 1 = 2 ^ n.size := by
  intro eq
  by_contra ne_pow2
  by_cases n_eq_0 : n = 0
  · simp [n_eq_0] at ne_pow2
  · replace n_eq_0 : n > 0 := zero_lt_of_ne_zero n_eq_0
    replace n_eq_0 : n ≥ 1 := n_eq_0
    by_cases n_eq_1 : n = 1
    · simp [n_eq_1, size] at ne_pow2
    · have n_ge_2 : n ≥ 2 := by
        refine (two_le_iff n).mpr ?_
        · constructor
          · exact Nat.ne_zero_of_lt n_eq_0
          · exact n_eq_1
      clear n_eq_0 n_eq_1
      have s1 : n + 1 < 2 ^ n.size := by
        simp at ne_pow2
        have : n < 2 ^ n.size := lt_size_self n
        replace : n + 1 ≤ 2 ^ n.size := this
        obtain lt|eq : n + 1 < 2 ^ n.size ∨ n + 1 = 2 ^ n.size := Or.symm (Nat.eq_or_lt_of_le this)
        · exact lt
        · exact absurd eq ne_pow2
      have s2 : (n + 1).size ≤ n.size := pow2_is_minimum n.size (n + 1) s1
      replace eq : (n + 1).size > n.size := by grind
      replace eq : ¬(n + 1).size ≤ n.size := Nat.not_le_of_lt eq
      exact absurd s2 eq

/--
The size of `n + 1` increases by 1 if and only if `n + 1` is a power of 2.
This characterizes exactly when the bit size increases.
-/
public theorem increase_n1size_iff_pow2 {n : ℕ} : (n + 1).size = n.size + 1 ↔ n + 1 = 2 ^ n.size := by
  constructor
  · exact increase_n1size_at_pow2
  · intro h ; exact size_of_pow2_eq_size_of_envelope_add_1 (Nat.eq_sub_of_add_eq h)

/--
The size of `n + 1` stays the same as `n.size` if and only if `n + 1` is not a power of 2.
This is the contrapositive of `increase_size_iff_pow2`.
-/
public theorem same_n1size_iff_not_pow2 {n : ℕ} : ¬n + 1 = 2 ^ n.size ↔ (n + 1).size = n.size := by
  have it {a b : Prop} : (a → b) → (¬b → ¬a) := fun a_1 a_2 a ↦ a_2 (a_1 a)
  constructor
  · intro p
    have : (n + 1).size = n.size + 1 → n + 1 = 2 ^ n.size := fun a ↦ increase_n1size_at_pow2 a
    replace this := it this p
    obtain q|q : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := size_limit n
    · exact q
    · exact absurd q this
  · intro p
    obtain q|q : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := size_limit n
    · replace q : ¬(n + 1).size = n.size + 1 := by simp [p]
      replace this := it increase_n1size_iff_pow2.mpr q
      exact this
    · simp [q] at p

/--
The size of n + 2 equals n.size if and only if both n + 2 and n + 1 are not powers of 2.
This is a two-step variant of same_size_iff_not_pow2.
-/
public theorem same_n2size_iff_not_pow2' {n : ℕ} :
    ¬n + 2 = 2 ^ n.size ∧ ¬n + 1 = 2 ^ n.size ↔ (n + 2).size = n.size := by
  constructor
  · intro ⟨h2, h1⟩
    have s1 : (n + 1).size = n.size := same_n1size_iff_not_pow2.mp h1
    have s2 : (n + 2).size = (n + 1).size := by
      exact same_n1size_iff_not_pow2.mp (ne_of_ne_of_eq h2 (congrArg (HPow.hPow 2) (id (Eq.symm s1))))
    simp [s2, s1]
  · intro h
    constructor
    · refine Nat.ne_of_lt ?_
      · by_contra x
        simp at x
        replace x : (2 ^ n.size).size ≤ (n + 2).size := size_le_size x
        rw [size_pow] at x
        replace x : n.size < (n + 2).size := x
        replace x : ¬(n + 2).size = n.size := Nat.ne_of_lt' x
        exact absurd h x
    · refine same_n1size_iff_not_pow2.mpr ?_
      · have s1 : (n + 2).size ≥ (n + 1).size := size_le_size (le_succ (n + 1))
        replace s1 : n.size ≥ (n + 1).size := by simp [h] at s1 ; exact s1
        have s2 : (n + 1).size ≥ n.size := size_le_size (le_succ n)
        exact Eq.symm (Nat.le_antisymm s2 s1)

public theorem increase_n2size_if_pow2₁ {n : ℕ} (h : n ≥ 4) :
    n + 1 = 2 ^ n.size → (n + 2).size = n.size + 1 := by
  intro h1
  have s1 : n + 1 + 1 = 2 ^ n.size + 1 := congrFun (congrArg HAdd.hAdd h1) 1
  have : n + 1 + 1 = n + 2 := rfl
  simp only [this] at s1
  simp [s1]
  replace : (2 ^ n.size + 1).size = n.size + 1 := by
    refine size_add Nat.one_pos ?_
    · exact Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp (size_pos.mpr (zero_lt_of_lt h)))
  exact this

public theorem increase_n2size_if_pow2₂ (n : ℕ) : n + 2 = 2 ^ n.size → (n + 2).size = n.size + 1 := by
  intro h2
  simp [h2, size_pow]

/--
For n ≥ 4, if `n + 2` is a power of 2, then its size is one more than `n.size`.
This is a variant of `increase_size_iff_pow2` specialized for the case of adding 2.
-/
theorem increase_n2size_if_pow2 {n : ℕ} (h : n ≥ 4) :
    n + 1 = 2 ^ n.size ∨ n + 2 = 2 ^ n.size → (n + 2).size = n.size + 1 := by
  rintro (h1|h2)
  · exact increase_n2size_if_pow2₁ h h1
  · exact increase_n2size_if_pow2₂ n h2

theorem increase_n2size_iff_pow2 {n : ℕ} (h : n ≥ 4) :
    n + 1 = 2 ^ n.size ∨ n + 2 = 2 ^ n.size ↔ (n + 2).size = n.size + 1 := by
  constructor
  · exact fun a ↦ increase_n2size_if_pow2 h a
  · intro n2size_eq_nsize_add_1
    by_cases n1_is_pow2 : n + 1 = 2 ^ n.size
    · left ; exact n1_is_pow2
    · have n1size_eq_nsize : (n + 1).size = n.size := same_n1size_iff_not_pow2.mp n1_is_pow2
      rw [←n1size_eq_nsize] at n2size_eq_nsize_add_1
      have n2 : n + 2 = n + 1 + 1 := rfl
      simp [n2] at n2size_eq_nsize_add_1
      have : n + 1 + 1 = 2 ^ (n + 1).size := increase_n1size_iff_pow2.mp n2size_eq_nsize_add_1
      rw [n1size_eq_nsize, ←n2] at this
      right
      exact this

/--
Lower bound on n based on its bit size. For any positive natural number n,
`2 ^ (n.size - 1) ≤ n`. This provides a lower bound relating n to its bit length.
-/
public theorem n_lower {n : ℕ} (n_gt_0 : n > 0) : 2 ^ (n.size - 1) ≤ n := by
  exact n_ge_subenvelope n_gt_0

/--
Stricter lower bound on n. For any natural number `n > 1`,
`2 ^ (n.size - 2) < n`. This is a tighter bound than n_lower.
-/
theorem n_lower' {n : ℕ} (n_bound : n > 1) : 2 ^ (n.size - 2) < n := by
  obtain n_eq_2|n_bound : n = 2 ∨ n > 2 := LE.le.eq_or_lt' n_bound
  · simp [n_eq_2]
  · obtain n_eq_3|n_bound : n = 3 ∨ n > 3 := LE.le.eq_or_lt' n_bound
    · simp [n_eq_3]
    · replace n_bound : n ≥ 4 := n_bound
      rename' n_bound => n_gt_4
      have nsize_ge_3 : n.size ≥ 3 := size4_add_0_ge_2 n_gt_4
      have lower : 2 ^ (n.size - 1) ≤ n := n_lower (zero_lt_of_lt n_gt_4)
      have : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 1) := by
        have s1 : 2 * 2 ^ (n.size - 2) = 2 ^ (n.size - 2 + 1) := Eq.symm Nat.pow_succ'
        have s2 : n.size - 2 + 1 = n.size - 1 := by
          refine Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) ?_)
          · exact Eq.symm (Nat.sub_add_cancel (le_of_add_left_le nsize_ge_3))
        simp [s2] at s1
        exact s1
      simp [←this] at lower
      rw [mul_comm, mul_two] at lower
      replace : 0 < 2 ^ (n.size - 2) := Nat.two_pow_pos (n.size - 2)
      replace : 1 ≤ 2 ^ (n.size - 2) := this
      replace : 2 ^ (n.size - 2) + 1 ≤ n := add_le_of_add_le_left lower this
      exact this
