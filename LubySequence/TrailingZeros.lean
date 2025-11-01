import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Size

open Finset Nat

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
The number of trailing zeros in 0 is 0.
-/
@[simp]
theorem trailing_zeros0 : trailing_zeros 0 = 0 := by simp [trailing_zeros]

/--
The number of trailing zeros in 1 is 0.
-/
@[simp]
theorem trailing_zeros1 : trailing_zeros 1 = 0 := by simp [trailing_zeros]

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
For n > 1 where n = 2^(n.size-1), the trailing zeros of n equals
the trailing zeros of (n - 2^(n.size-2)) plus 1.
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
      <;> { simp [n₂] }
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
