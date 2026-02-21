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
The length of the bit representation equals the size of a natural number.
-/
public theorem bitslength_eq_size (n : ℕ) : n.bits.length = n.size := by exact size_eq_bits_len n

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
Every natural number less than `2 ^ k` has size at most k.
-/
public theorem pow2_is_minimum (k : ℕ) : ∀ n < ((2 : ℕ) ^ k) , n.size ≤ k := by
  intro n hn
  have t1 : n.size ≤ (2 ^ k).size := size_le_size (le_of_succ_le hn)
  have t2 : (2 ^ k).size = k + 1 := size_of_pow2_eq_self_add_one k
  simp [t2] at t1
  exact size_le.mpr hn

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
