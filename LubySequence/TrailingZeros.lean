module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import LubySequence.Size

open Finset Nat

attribute [local simp] binaryRec

/--
Returns the number of zeros at the end of bit representation of Nat `n`.
Note: `trailing_zeros 0 = 0`
It differs from the Rust implementation which returns 64 if n = 0_u64.
-/
@[expose]
public def trailing_zeros (n : ℕ) : ℕ := match h : n with
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
The number of trailing zeros in 1 is 0.
-/
@[simp]
public theorem trailing_zeros1 : trailing_zeros 1 = 0 := by simp [trailing_zeros]

/--
Returns the number of consecutive ones at the end of bit representation of Nat `n`.
For example, `trailing_ones 7 = 3` since 7 in binary is 111.
-/
def trailing_ones (n : ℕ) : ℕ :=
  if h : n < 2
  then n
  else if n % 2 = 1 then 1 + trailing_ones (n / 2) else 0

  /--
The number of trailing zeros in 2^n equals n.
-/
theorem trailing_zeros_of_envelope : ∀ n : ℕ, trailing_zeros (2 ^ n) = n := by
  intro n
  induction n with
  | zero => simp [trailing_zeros.eq_def]
  | succ n hn' =>
    rw [trailing_zeros.eq_def]
    split <;> expose_names
    · have c : ¬2 ^ (n + 1) = 0 := NeZero.ne (2 ^ (n + 1))
      exact absurd heq c
    · have n2 : (2 ^ (n + 1)).size = n + 2 := size_of_pow2_eq_self_add_one (n + 1)
      split <;> expose_names
      · simp [n2]
      · simp [n2] at h

/--
For n > 1 where n = 2^(n.size-1), the trailing zeros of n equals
the trailing zeros of (n - 2^(n.size-2)) plus 1.
-/
theorem trailing_zeros_prop2 :
    ∀ n : ℕ, n > 1 → n = 2 ^ (n.size - 1) → trailing_zeros (n - 2 ^ (n.size - 2)) + 1 = trailing_zeros n := by
  intro n hn1 hn2
  have n2 : 2 ≤ n.size := by
    have t1 : (2 : ℕ).size ≤ n.size := size_le_size hn1
    have t2 : (2 : ℕ).size = 2 := by simp [size]
    exact le_of_eq_of_le (id (Eq.symm t2)) t1
  have t1 : trailing_zeros n = n.size - 1 := by
    rewrite (occs := .pos [1]) [hn2]
    exact trailing_zeros_of_envelope (n.size - 1)
  have t2 : n - 2 ^ (n.size - 2) = 2 ^ (n.size - 2) := by
    rewrite (occs := .pos [1]) [hn2]
    refine Nat.sub_eq_of_eq_add ?_
    rw [←mul_two]
    have : 2 ^ (n.size - 2) * 2 = 2 ^ (n.size - 2 + 1) := rfl
    simp [this]
    exact (Nat.sub_eq_iff_eq_add n2).mp rfl
  simp [t1, t2]
  have : trailing_zeros (2 ^ (n.size - 2)) = n.size - 2 := trailing_zeros_of_envelope (n.size - 2)
  simp [this]
  grind

/--
The number of trailing zeros in 2^n equals n.
-/
public theorem trailing_zeros_prop3 : ∀ n : ℕ, trailing_zeros (2 ^ n) = n := by
  intro n
  rw [trailing_zeros.eq_def]
  split <;> expose_names
  · have : ¬2 ^ n = 0 := by exact NeZero.ne (2 ^ n)
    exact absurd heq this
  · split <;> expose_names
    · rw [h]
      have t1 : (2 ^ ((2 ^ n).size - 1)).size = (2 ^ n).size - 1 + 1 := by
        exact size_of_pow2_eq_self_add_one ((2 ^ n).size - 1)
      simp [t1]
      have t2 : (2 ^ n).size = n + 1 := by exact size_of_pow2_eq_self_add_one n
      exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm t2)))
    · have t1 : (2 ^ n).size = n + 1 := by exact size_of_pow2_eq_self_add_one n
      simp [t1] at h

/--
Powers of 2 plus 1 cannot equal other powers of 2 (contradiction lemma).
-/
theorem parity_unmatch {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2 ^ a + 1 = 2 ^ b) : false := by
  have two_pow_a_is_even : 2 ∣ 2 ^ a := by exact dvd_pow_self 2 (ne_zero_of_lt ha)
  have even : 2 ∣ 2 ^ a + 1 := by
    simp [h]
    exact Nat.ne_zero_of_lt hb
  have odd : ¬2 ∣ 2 ^ a + 1 := by
    exact Odd.not_two_dvd_nat (Even.add_one ((even_iff_exists_two_nsmul (2 ^ a)).mpr two_pow_a_is_even))
  exact absurd even odd

/--
For k < 2^n and k ≠ 0, trailing_zeros(k + 2^n) = trailing_zeros(k).
-/
public theorem trailing_zeros_prop7 : ∀ n : ℕ, ∀ k < 2 ^ n,
    ¬k = 0 → trailing_zeros (k + 2 ^ n) = trailing_zeros k := by
  intro n k
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k' h1
    rw [trailing_zeros.eq_def]
    split
    · expose_names
      have c : ¬k + 2 ^ n = 0 := by
        have : 0 < 2 ^ n := Nat.two_pow_pos n
        exact NeZero.ne (k + 2 ^ n)
      exact absurd heq c
    · obtain z|p : n = 0 ∨ 0 < n := Nat.eq_zero_or_pos n
      · simp [z] at *
        exact absurd k' h1
      · have n2 : (2 ^ n).size = n + 1 := size_of_pow2_eq_self_add_one n
        have s1 : 2 ^ n + k < 2 ^ n + 2 ^ n := Nat.add_lt_add_left k' (2 ^ n)
        rw [←mul_two] at s1
        have so : (2 ^ n + k).size = n + 1 := by
          have left : n + 1 ≤ (2 ^ n + k).size := by
            have : (2 ^ n).size ≤ (2 ^ n + k).size := size_le_size (le_add_right (2 ^ n) k)
            exact le_of_eq_of_le (id (Eq.symm n2)) this
          have right : (2 ^ n + k).size ≤ n + 1 := pow2_is_minimum (n + 1) (2 ^ n + k) s1
          exact Eq.symm (le_antisymm left right)
        have eq_size : (2 ^ n + k).size = (2 ^ n).size := by
          refine size_add' (by grind) ?_
          · have s4 : (2 ^ n + k).size = (2 ^ n).size := by simp [so, n2]
            simp [s4]
        split <;> expose_names
        · have t1 : 2 ^ n < k + 2 ^ n := Nat.lt_add_of_pos_left (zero_lt_of_ne_zero h1)
          have t2 : 2 ^ n = 2 ^ ((2 ^ n).size - 1) := by
            have : (2 ^ n).size = n + 1 := size_of_pow2_eq_self_add_one n
            simp [this]
          rewrite (occs := .pos [1]) [t2] at t1
          clear t2
          simp [←eq_size] at t1
          rewrite (occs := .pos [1]) [add_comm] at t1
          have c : ¬k + 2 ^ n = 2 ^ ((k + 2 ^ n).size - 1) := Nat.ne_of_lt' t1
          exact absurd h c
        · simp
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
public theorem trailing_zeros_prop8 : ∀ n : ℕ, ∀ k ≤ 2 ^ n,
    ∑ i ∈ range (k - 1), (trailing_zeros (2 ^ n + i + 1) + 1)
    = ∑ i ∈ range (k - 1), (trailing_zeros (      i + 1) + 1) := by
  intro n k hk
  let f1 := (fun i ↦ if h : i < 2 ^ n then trailing_zeros (i + 2 ^ n) else 0)
  have f1_def : f1 = value_of% f1 := rfl
  have f1eq : f1 = (fun i ↦
      if h : i < 2 ^ n
      then if h' : i == 0 then trailing_zeros (2 ^ n) else trailing_zeros i
      else 0) := by
    simp [f1_def]
    ext x
    split <;> expose_names
    · split <;> expose_names
      · simp [h_1]
      · exact trailing_zeros_prop7 n x h h_1
    · simp at h ; exact rfl
  have t1 :
     (∑ x ∈ range (k - 1), (trailing_zeros (2 ^ n + x + 1) + 1)) =
     (∑ x ∈ range (k - 1), (f1             (        x + 1) + 1)) := by
    simp [f1_def]
    refine sum_congr rfl ?_
    · intro y hy
      split <;> expose_names
      · have : 2 ^ n + y + 1 = y + 1 + 2 ^ n := by grind
        simp [this]
      · have    t1 : y     < k - 1 := List.mem_range.mp hy
        replace t1 : y + 1 < k     := add_lt_of_lt_sub t1
        replace t1 : y + 1 < 2 ^ n := lt_of_lt_of_le t1 hk
        exact absurd t1 h
  simp [t1]
  clear t1
  let f2 := (fun i ↦ if h : (i + 1) < 2 ^ n then trailing_zeros ((i + 1) + 2 ^ n) else 0)
  have f2_def : f2 = value_of% f2 := rfl
  have t2 :
      (∑ i ∈ range (k - 1), (f1 (i + 1) + 1)) =
      (∑ i ∈ range (k - 1), (f2  i      + 1)) := by
    exact rfl
  simp [t2]
  let f3 := (fun i ↦ if h : i +1 < 2 ^ n then trailing_zeros (i + 1) else 0)
  have f3_def : f3 = value_of% f3 := rfl
  have f2eqf3 : f2 = f3 := by
    simp [f2_def, f3_def]
    ext i
    split
    · expose_names ; exact trailing_zeros_prop7 n (i + 1) h (by grind)
    · exact rfl
  simp [f2eqf3]
  have t3 :
     (∑ i ∈ range (k - 1), (trailing_zeros (i + 1) + 1)) =
     (∑ i ∈ range (k - 1), (f3              i + 1)) := by
    simp [f3_def]
    refine sum_congr rfl ?_
    · intro y hy
      split <;> expose_names
      · exact rfl
      · have    t1 : y     < k - 1 := List.mem_range.mp hy
        replace t1 : y + 1 < k     := add_lt_of_lt_sub t1
        replace t1 : y + 1 < 2 ^ n := lt_of_lt_of_le t1 hk
        exact absurd t1 h
  simp [t3]

/--
For `k < 2 ^ n`, the sum of `(trailing_zeros (2 ^ n + i + 1) + 1)` over i in range k equals
the sum of `(trailing_zeros (i + 1) + 1)` over the same range.
This is a strict version of `trailing_zeros_prop8` using strict inequality.
-/
public theorem trailing_zeros_prop9 : ∀ n : ℕ, ∀ k < 2 ^ n,
    ∑ i ∈ range k, (trailing_zeros (2 ^ n + i + 1) + 1) = ∑ i ∈ range k, (trailing_zeros (i + 1) + 1) := by
  intro n k' k_lt_pow2
  let k := k' + 1
  have k_def : k = value_of% k := rfl
  replace k_def : k' = k - 1 := by grind
  simp [k_def] at *
  exact trailing_zeros_prop8 n k k_lt_pow2

-- #eval List.range 6
--    |>.map (fun n ↦ 2 ^ n)
--    |>.map (fun n ↦ (n, range n, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1), 2 * n - 1))

-- The following was proved by Aristotle:
public theorem sum_of_trailing_zeros_prop :
    ∀ n : ℕ, n = (2 : ℕ) ^ (n.size - 1) → ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) = (2 : ℕ) * n - 1 := by
  intro n hn
  have h_sum_powers_of_two : ∀ k : ℕ, ∑ i ∈ Finset.range (2 ^ k), (trailing_zeros (i + 1) + 1) = 2 * 2 ^ k - 1 := by
    -- We proceed by induction on $k$.
    intro k
    induction' k with k ih;
    · native_decide +revert;
    · rw [ pow_succ' ];
      -- We can split the sum into two parts: the sum over the first half and the sum over the second half.
      have h_split : ∑ i ∈ Finset.range (2 * 2 ^ k), (trailing_zeros (i + 1) + 1) = (∑ i ∈ Finset.range (2 ^ k), (trailing_zeros (i + 1) + 1)) + (∑ i ∈ Finset.range (2 ^ k), (trailing_zeros (2 ^ k + i + 1) + 1)) := by
        rw [ two_mul, Finset.sum_range_add ];
      -- By the properties of trailing zeros, we can simplify the second sum.
      have h_simplify : ∑ i ∈ Finset.range (2 ^ k), (trailing_zeros (2 ^ k + i + 1) + 1) = ∑ i ∈ Finset.range (2 ^ k), (trailing_zeros (i + 1) + 1) + 1 := by
        have h_simplify : ∀ i ∈ Finset.range (2 ^ k), trailing_zeros (2 ^ k + i + 1) = trailing_zeros (i + 1) + (if i + 1 = 2 ^ k then 1 else 0) := by
          intro i hi; split_ifs <;> simp_all +singlePass [ add_comm, add_left_comm ] ;
          · rw [ show i + ( 1 + 2 ^ k ) = 2 ^ k + 2 ^ k by linarith ] ; simp +arith +decide [ *, trailing_zeros_prop3 ] ; ring_nf;
            convert trailing_zeros_prop3 ( k + 1 ) using 1 ; ring;
          · convert trailing_zeros_prop7 k ( i + 1 ) _ _ using 1 <;> norm_num [ add_comm, add_left_comm, add_assoc ];
            exact lt_of_le_of_ne hi ( by tauto );
        rw [ Finset.sum_congr rfl fun i hi => by rw [ h_simplify i hi ] ] ; simp +arith +decide [ Finset.sum_add_distrib ] ; ring_nf;
        rw [
          show { x ∈ Finset.range ( 2 ^ k ) | 1 + x = 2 ^ k } = { 2 ^ k - 1 } from
            Finset.eq_singleton_iff_unique_mem.mpr ⟨
              Finset.mem_filter.mpr ⟨
                Finset.mem_range.mpr ( Nat.sub_lt ( by norm_num ) ( by norm_num ) ),
                by rw [ add_tsub_cancel_of_le ( Nat.one_le_pow _ _ ( by norm_num ) ) ] ⟩,
              fun x hx => by linarith [ Finset.mem_filter.mp hx, Nat.sub_add_cancel ( Nat.one_le_pow k 2 ( by norm_num ) ) ] ⟩
           ] ; norm_num ; -- ring;
      exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show 0 < 2 * 2 ^ k from by positivity ) ] );
  grind
