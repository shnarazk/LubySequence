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
The number of trailing zeros in 0 is 0.
-/
@[simp]
public theorem trailing_zeros0 : trailing_zeros 0 = 0 := by simp [trailing_zeros]

/--
The number of trailing zeros in 1 is 0.
-/
@[simp]
public theorem trailing_zeros1 : trailing_zeros 1 = 0 := by simp [trailing_zeros]

/--
The number of trailing zeros in 2 is 1.
-/
@[simp]
public theorem trailing_zeros2 : trailing_zeros 2 = 1 := by simp [trailing_zeros]

/--
The number of trailing zeros in 3 is 0.
-/
@[simp]
public theorem trailing_zeros3 : trailing_zeros 3 = 0 := by simp [trailing_zeros]

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
public theorem trailing_zeros_of_envelope : ∀ n : ℕ, trailing_zeros (2 ^ n) = n := by
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
For positive n not equal to 2^(n.size-1), trailing_zeros(n) = trailing_zeros(n - 2^(n.size-1)).
-/
public theorem trailing_zeros_prop1 : ∀ n > 0,
    ¬n = 2 ^ (n.size - 1) → trailing_zeros n = trailing_zeros (n - 2 ^ (n.size - 1)) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro n_ne_envenlop
    rw [trailing_zeros.eq_def]
    split
    · contradiction
    · split <;> expose_names
      · exact absurd h n_ne_envenlop
      · exact rfl

/--
For positive n and k where 2^k > n, adding 2^k to n preserves the number of trailing zeros.
This shows that adding a sufficiently large power of 2 does not affect trailing zeros.
-/
public theorem trailing_zeros_prop1' : ∀ n > 0, ∀ k : ℕ,
    2 ^ k > n → trailing_zeros (n + 2 ^ k) = trailing_zeros n := by
  intro n n_gt_0 k pow2k_gt_n
  rw [trailing_zeros.eq_def]
  split <;> expose_names
  · have n_eq_0 : n = 0 := Nat.eq_zero_of_add_eq_zero_right heq
    replace n_gt_0 : ¬n = 0 := Nat.ne_zero_of_lt n_gt_0
    exact absurd n_eq_0 n_gt_0
  · split <;> expose_names
    · have : 2 ^ (k + 1) = 2 ^ ((n + 2 ^ k).size - 1) := by
        have : (2 ^ k + n).size = k + 1 := size_add n_gt_0 pow2k_gt_n
        rw (occs := .pos [2]) [add_comm] at h
        simp [this] at h
        replace n_gt_0 : ¬n = 0 := Nat.ne_zero_of_lt n_gt_0
        exact absurd h n_gt_0
      rw (occs := .pos [1]) [←this] at h
      replace : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := two_pow_succ k
      simp [this] at h
      have h' : ¬n = 2 ^ k := Nat.ne_of_lt pow2k_gt_n
      exact absurd h h'
    · simp
      have : 2 ^ ((n + 2 ^ k).size - 1) = 2 ^ k := by
        have : (2 ^ k + n).size = k + 1 := size_add n_gt_0 pow2k_gt_n
        rw (occs := .pos [1]) [add_comm] at this
        simp [this]
      simp [this]

/--
For n > 1 where n = 2^(n.size-1), the trailing zeros of n equals
the trailing zeros of (n - 2^(n.size-2)) plus 1.
-/
public theorem trailing_zeros_prop2 :
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
The number of trailing zeros in 2^n - 1 is always 0.
-/
public theorem trailing_zeros_prop4 : ∀ n : ℕ, trailing_zeros (2 ^ n - 1) = 0 := by
  intro n
  induction n with
  | zero => simp [trailing_zeros.eq_def]
  | succ n hn =>
    rw [trailing_zeros.eq_def]
    split <;> expose_names
    · exact heq
    · split <;> expose_names
      · have t1 : (2 ^ (n + 1) - 1).size = n + 1 := by
          exact size_sub ( zero_lt_succ n) one_pos Nat.one_le_two_pow
        simp [t1] at h
        obtain z|p : n = 0 ∨ ¬n = 0 := Or.symm (ne_or_eq n 0)
        · simp [z] at *
        · have even : 2 ∣ 2 ^ n := Dvd.dvd.pow (by grind) p
          have odd : ¬2 ∣ 2 ^ (n + 1) := by
            simp [←h] at even
            refine two_dvd_ne_zero.mpr ?_
            have h' : 2 ^ (n + 1) = 2 ^ n + 1 := by grind
            simp [h']
            grind
          have even' : 2 ∣ 2 ^ (n + 1) := Dvd.intro_left (Nat.pow 2 n) rfl
          exact absurd even' odd
      · simp
        have : 2 ^ (n + 1) - 1 - 2 ^ ((2 ^ (n + 1) - 1).size - 1) = 2 ^ n - 1 := by
          have t1 : (2 ^ (n + 1) - 1).size = n + 1 := size_sub (by grind) (by grind) (by grind)
          simp [t1]
          replace t1 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by grind
          simp [t1]
          grind
        simp [this]
        exact hn

/--
Powers of 2 plus 1 cannot equal other powers of 2 (contradiction lemma).
-/
public theorem parity_unmatch {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2 ^ a + 1 = 2 ^ b) : false := by
  have two_pow_a_is_even : 2 ∣ 2 ^ a := by exact dvd_pow_self 2 (ne_zero_of_lt ha)
  have even : 2 ∣ 2 ^ a + 1 := by
    simp [h]
    exact Nat.ne_zero_of_lt hb
  have odd : ¬2 ∣ 2 ^ a + 1 := by
    exact Odd.not_two_dvd_nat (Even.add_one ((even_iff_exists_two_nsmul (2 ^ a)).mpr two_pow_a_is_even))
  exact absurd even odd

/--
The number of trailing zeros in 2^(n+1) + 1 is always 0.
TODO: no need to induction
-/
public theorem trailing_zeros_prop5 : ∀ n : ℕ, trailing_zeros (2 ^ (n + 1) + 1) = 0 := by
  intro n
  induction n with
  | zero =>
    simp
  | succ n hn =>
    rw [trailing_zeros]
    split
    · expose_names
      simp at h
      have sub1 : 0 < n + 1 + 1 := by grind
      have sub2 : 0 < (2 ^ (n + 1 + 1) + 1).size - 1 := by
        have t1 : 2 ≤ n + 1 + 1 := by grind
        replace t1 : 2 ^ 2 ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by grind) t1
        have t2 : 2 ^ 2 = 4 := by grind
        simp [t2] at t1
        replace t1 : 4 + 1 ≤ 2 ^ (n + 1 + 1) + 1 := Nat.add_le_add_iff_right.mpr t1
        replace t1 : (4 + 1).size ≤ (2 ^ (n + 1 + 1) + 1).size := size_le_size t1
        simp at t1
        rewrite (occs := .pos [1]) [size] at t1
        simp at t1
        have t1 : 2 ≤ (2 ^ (n + 1 + 1) + 1).size - 1 := le_sub_one_of_lt t1
        exact zero_lt_of_lt t1
      have c := parity_unmatch sub1 sub2 h
      simp at c
    · simp
      have t1 : (2 ^ (n + 1 + 1) + 1).size = n + 1 + 1 + 1 := by
        exact size_add (by grind) (one_lt_two_pow' (n + 1))
      simp [t1]

/--
For positive n not equal to 2^(n.size-1), trailing_zeros(n) = trailing_zeros(n - 2^(n.size-1)).
-/
public theorem trailing_zeros_prop6 : ∀ n > 0,
    ¬n = 2 ^ (n.size - 1) → trailing_zeros n = trailing_zeros (n - 2 ^ (n.size - 1)) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn'
    rw [trailing_zeros.eq_def]
    split
    · contradiction
    · split <;> expose_names
      · exact absurd h hn'
      · simp

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
public theorem size_of_even_add_one_eq_size_of_self : ∀ n > 0,
    ((2 : ℕ) * n).size = ((2 : ℕ) * n + 1).size := by
  intro n h
  let bv := n.bits
  have hbv : bv = value_of% bv := rfl
  have two0 : (2 * n).bits = false :: bv := bits_of_double_eq_cons_false_and_bits n h
  have two1 : (2 * n + 1).bits = true :: bv := bit1_bits n
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
public theorem trailing_zeros_of_pow2_is_max : ∀ n ≥ 2, n = 2 ^ (n.size - 1) →
    ∀ n' < n, trailing_zeros n' < trailing_zeros n := by
  intro n hn
  have nsize2 : n.size ≥ 2 := by
    have t1 : (2 : ℕ).size ≤ n.size := size_le_size hn
    have t2 : (2 : ℕ).size = 2 := by simp [size]
    simp [t2] at t1
    exact t1
  induction n using Nat.strong_induction_on with
  | h n hn' =>
    intro n₁ n₂ hn'2
    let m := 2 ^ (n.size - 2)
    have hm : m = value_of% m := rfl
    obtain n_eq_two|n_gt_two : n = 2 ∨ n > 2 := by
      refine Nat.eq_or_lt_of_not_lt ?_
      · simp
        exact hn
    · simp [n_eq_two] at *
      obtain n₂|n₂ : n₂ = 0 ∨ n₂ = 1 := le_one_iff_eq_zero_or_eq_one.mp (le_of_lt_succ hn'2)
      <;> { simp [n₂] }
    · have sub1 : m < n := by
        refine le_if_le_size ?_
        · simp [hm]
          have : (2 ^ (n.size - 2)).size = n.size - 2 + 1 := by
            exact size_of_pow2_eq_self_add_one (n.size - 2)
          simp [this]
          grind
      have n4 : n ≥ 4 := by
        obtain n_eq_3|n_gt_3 : n = 3 ∨ n > 3 := LE.le.eq_or_lt' n_gt_two
        · simp [n_eq_3] at *
        · exact n_gt_3
      have n4size : n.size ≥ 3 := by
        have t1 : n.size ≥ (4 : ℕ).size := size_le_size n4
        have t2 : (4 : ℕ).size = 3 := by simp [size]
        simp [t2] at t1
        exact t1
      have sub2 : m ≥ 2 := Nat.le_self_pow (Nat.sub_ne_zero_iff_lt.mpr n4size) 2
      have sub3 : m.size ≥ 2 := by
        have t1 : m.size ≥ (2 : ℕ).size := size_le_size sub2
        have t2 : (2 : ℕ).size = 2 := by simp [size]
        simp [t2] at t1
        exact t1
      have sub4 : m = 2 ^ (m.size - 1) := by
        simp [hm]
        have t1 : (2 ^ (n.size - 2)).size = n.size - 2 + 1 := by
          exact size_of_pow2_eq_self_add_one (n.size - 2)
        simp [t1]
      have trailing_zeros_m : trailing_zeros m = n.size - 2 := by
        simp [hm]
        exact trailing_zeros_prop3 (n.size - 2)
      have trailing_zeros_n : trailing_zeros n = n.size - 1 := by
        rewrite (occs := .pos [1]) [n₁]
        exact trailing_zeros_prop3 (n.size - 1)
      obtain first_part|others : n₂ < m ∨ n₂ ≥ m := Nat.lt_or_ge n₂ m
      · have trans1 : trailing_zeros m < trailing_zeros n := by
          simp [trailing_zeros_m, trailing_zeros_n]
          exact sub_succ_lt_self n.size 1 nsize2
        have g := hn' m sub1 sub2 sub3 sub4 n₂ first_part
        have trans2 : trailing_zeros n₂ < trailing_zeros m := g
        exact Nat.lt_trans g trans1
      · obtain n₂_eq_m|n₂_gt_m : n₂ = m ∨ n₂ > m := LE.le.eq_or_lt' others
        · simp [n₂_eq_m] at *
          simp [trailing_zeros_m, trailing_zeros_n]
          exact sub_succ_lt_self n.size 1 nsize2
        · -- slide to the left
          let n₂' := n₂ - m
          have n₂_def : n₂' = value_of% n₂' := rfl
          have n₂_def' : n₂ = 2 ^ (m.size - 1) + n₂' := by
            simp [←sub4]
            exact Eq.symm (add_sub_of_le others)
          have n₂'_range : n₂' < m := by
            have t1 : m + m = n := by
              simp [hm]
              calc
                2 ^ (n.size - 2) + 2 ^ (n.size - 2) = 2 ^ (n.size - 2) * 2 := by
                  exact Eq.symm (Nat.mul_two (2 ^ (n.size - 2)))
                _ = 2 ^ (n.size - 2 + 1) := rfl
                _ = 2 ^ (n.size - 1) := by
                  have : n.size - 2 + 1 = n.size - 1 := by
                    refine Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) ?_)
                    exact (Nat.sub_eq_iff_eq_add nsize2).mp rfl
                  simp [this]
                _ = n := by simp [←n₁]
            have t2 : n₂ = n₂' + m := (Nat.sub_eq_iff_eq_add others).mp n₂_def
            simp [←t1, t2] at hn'2
            exact hn'2
          have shift_left : trailing_zeros n₂ = trailing_zeros n₂' := by
            rewrite [n₂_def', add_comm]
            refine trailing_zeros_prop7 (m.size - 1) n₂' ?_ ?_
            · simp [←sub4] ; exact n₂'_range
            · by_contra h
              simp [h] at *
              have c : n₂ = m := by grind
              have : ¬n₂ = m := Nat.ne_of_lt' n₂_gt_m
              exact absurd c this
          simp [shift_left]
          have g := hn' m sub1 sub2 sub3 sub4 n₂' n₂'_range
          have g' : trailing_zeros m < trailing_zeros n := by
            simp [trailing_zeros_m, trailing_zeros_n]
            exact sub_succ_lt_self n.size 1 nsize2
          exact Nat.lt_trans g g'

-- #eval List.range 6
--    |>.map (fun n ↦ 2 ^ n)
--    |>.map (fun n ↦ (n, range n, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1), 2 * n - 1))

/--
FIXME: there's no `n` such that `n = 2 ^ n.size`.
For any `n` that is exactly a power of two, the cumulative count of trailing zeros (plus one)
over the interval `1 ≤ i ≤ n - 1` matches the closed form `2 * n - 1`. This acts as a sanity
check for telescoping arguments that shift ranges by powers of two in later parts of the file.
-/
public theorem sum_of_trailing_zeros_prop_useless :
    ∀ n : ℕ, n = (2 : ℕ) ^ n.size → ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) = (2 : ℕ) * n - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro n_is_pow2
    obtain n_eq_0|n_gt_0 : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
    · simp [n_eq_0]
    · replace ih := ih (n / 2) (by grind)
      have nsize_ge_1 : n.size ≥ 1 := one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (size_pos.mpr n_gt_0))
      have nsize_pm : n.size - 1 + 1 = n.size := by exact Nat.sub_add_cancel nsize_ge_1
      have even : Even n := by
        rw [n_is_pow2]
        exact (even_pow' (Nat.pos_iff_ne_zero.mp (size_pos.mpr n_gt_0))).mpr (even_iff.mpr rfl)
      have : n / 2 = 2 ^ (n / 2).size := by
        rw (occs := .pos [1]) [n_is_pow2]
        have left : 2 ^ n.size / 2 = 2 ^ (n.size - 1) := by
          refine Nat.div_eq_of_eq_mul_left Nat.two_pos ?_
          · rw [←pow_succ]
            exact congrArg (HPow.hPow 2) (id (Eq.symm nsize_pm))
        have right : 2 ^ (n / 2).size = 2 ^ (n.size - 1) := by
          exact (Nat.pow_right_inj (Nat.one_lt_two)).mpr (size_div n_gt_0 (Even.two_dvd even))
        simp [left, right]
      replace ih := ih this
      replace : n = n / 2 + n / 2 := by grind
      rw [this]
      rw [sum_range_add]
      rw [ih, mul_add]
      replace : 2 * (n / 2) = n := by grind
      simp [this]
      replace : n / 2 = (n / 2 - 1) + 1 := by
        refine Eq.symm (Nat.sub_add_cancel ?_)
        · obtain n_eq_1|n_ge_2 : n = 1 ∨ n > 1 := Or.symm (Decidable.lt_or_eq_of_le' n_gt_0)
          · replace : Odd n := ZMod.natCast_eq_one_iff_odd.mp (congrArg Nat.cast n_eq_1)
            replace : ¬Even n := by exact not_even_iff_odd.mpr this
            exact absurd even this
          · replace n_ge_2 : n ≥ 2 := n_ge_2
            grind
      rw [this]
      rw [sum_range_add]
      simp
      replace : ∑ x ∈ range (n / 2 - 1), (trailing_zeros (n / 2 - 1 + 1 + x + 1) + 1) =
          ∑ x ∈ range (n / 2 - 1), (trailing_zeros (n / 2 + x + 1) + 1) := by
        refine sum_equiv ?_ (fun i ↦ ?_) ?_
        · exact Denumerable.eqv ℕ
        · exact Iff.of_eq rfl
        · intro i i_def
          refine Nat.add_right_cancel_iff.mpr ?_
          · have : n / 2 - 1 + 1 + i + 1 = n / 2 + (Denumerable.eqv ℕ) i + 1 := by
              exact congrFun (congrArg HAdd.hAdd (congrFun (congrArg HAdd.hAdd (id (Eq.symm this))) i)) 1
            exact congrArg trailing_zeros this
      simp [this]
      have n2_def : n / 2 = 2 ^ (n.size - 1) := by
        rw (occs := .pos [1]) [n_is_pow2]
        refine Nat.div_eq_of_eq_mul_left ?_ ?_
        · exact Nat.two_pos
        · exact Eq.symm (Nat.pow_pred_mul (size_pos.mpr n_gt_0))
      rw [n2_def]
      replace : ∑ x ∈ range (2 ^ (n.size - 1) - 1), (trailing_zeros (2 ^ (n.size - 1) + x + 1) + 1) =
          ∑ x ∈ range (2 ^ (n.size - 1) - 1), (trailing_zeros (x + 1) + 1) := by
        refine trailing_zeros_prop8 (n.size - 1) (2 ^ (n.size - 1)) ?_
        · exact Nat.le_refl (2 ^ (n.size - 1))
      simp [this]
      have aux2 : 2 ^ (n.size - 1) ≥ 1 := by exact Nat.one_le_two_pow
      replace : 2 ^ (n.size - 1) - 1 + 1 = 2 ^ (n.size - 1) := Nat.sub_add_cancel aux2
      simp [this]
      replace : 2 ^ (n.size - 1) + (2 ^ (n.size - 1) - 1) = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) - 1 := by
        exact Eq.symm (Nat.add_sub_assoc aux2 (2 ^ (n.size - 1)))
      simp [this, ←mul_two]
      replace : 2 ^ (n.size - 1) * 2 - 1 + 1 = 2 ^ (n.size - 1) * 2 := by grind
      simp [this]
      replace : trailing_zeros (2 ^ (n.size - 1) * 2) = trailing_zeros (2 ^ (n.size - 1)) + 1 := by
        have left : trailing_zeros (2 ^ (n.size - 1) * 2) = n.size := by
          rw [←pow_succ]
          simp [nsize_pm]
          exact trailing_zeros_prop3 n.size
        have right : trailing_zeros (2 ^ (n.size - 1)) + 1 = n.size := by
          rw [trailing_zeros_prop3 (n.size - 1)]
          exact nsize_pm
        simp [left, right]
      simp [this]
      have : ∑ x ∈ range (2 ^ (n.size - 1) - 1), (trailing_zeros (x + 1) + 1) + (trailing_zeros (2 ^ (n.size - 1)) + 1 + 1) =
          ∑ x ∈ range (2 ^ (n.size - 1) - 1), (trailing_zeros (x + 1) + 1) + (trailing_zeros (2 ^ (n.size - 1)) + 1) + 1 := by
        rfl
      simp [this]
      replace : ∑ x ∈ range (2 ^ (n.size - 1) - 1), (trailing_zeros (x + 1) + 1) +
          (trailing_zeros (2 ^ (n.size - 1) - 1 + 1) + 1) =
          ∑ x ∈ range (2 ^ (n.size - 1) - 1 + 1), (trailing_zeros (x + 1) + 1) := by
        exact Eq.symm (sum_range_succ (fun x ↦ trailing_zeros (x + 1) + 1) (2 ^ (n.size - 1) - 1))
      have aux : 2 ^ (n.size - 1) - 1 + 1 = 2 ^ (n.size - 1) := Nat.sub_add_cancel aux2
      simp [aux] at this
      simp [this]
      simp [←n2_def]
      simp [ih]
      grind

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
