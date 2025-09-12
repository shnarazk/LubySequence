import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

open Finset

/--
Returns the number of zeros at the end of bit representation of Nat `n`.
Note: `trailing_zeros 0 = 0`
It differs from the Rust implementation which returns 64 if n = 0_u64.
--/
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
        exact Nat.sub_lt n1 t1
      trailing_zeros (n - 2 ^ (n.size - 1))
  -- | _ => if n < 2 then 0 else if n % 2 = 0 then 1 + trailing_zeros (n / 2) else 0

-- #eval List.range 9 |>.map (fun n ↦ (n, trailing_zeros n))

def trailing_ones (n : ℕ) : ℕ :=
  if h : n < 2
  then n
  else if n % 2 = 1 then 1 + trailing_ones (n / 2) else 0

def scanList {α : Type _} (f : α → α) (init : α) (n : ℕ) (start : Bool := true) : List α :=
  match n with
  | 0      => []
  | n' + 1 =>
    let nxt := f init
    if start
      then init :: nxt :: scanList f nxt n' false
      else nxt :: scanList f nxt n' false

-- #eval scanList (· + 1) 10 8

theorem self_ne_pow_two_succ_of_size (n : ℕ) : n < 2 ^ n.size.succ := by exact Nat.size_le.mp (by grind)

theorem mod_gt_right (a b : ℕ) (h : 0 < b) : a % b < b := by exact Nat.mod_lt a h
theorem mod_eq_left {a b : ℕ} (ha : a < b) : a % b = a := by exact Nat.mod_eq_of_lt ha

theorem mod_gt_right' {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : a % b = 0 → (a - 1) % b + 1 = b := by
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
        · have a0 : a = 0 := by exact Nat.eq_zero_of_dvd_of_div_eq_zero h t
          have : ¬ 0 < a := by exact Eq.not_gt a0
          exact absurd ha this
        · have : 1 ≤ a / b := by exact Nat.one_le_iff_ne_zero.mpr f
          exact this
      _ = (a / b - 1) * b + 1 * b := by exact Nat.add_mul (a / b - 1) 1 b
      _ = (a / b - 1) * b + b := by grind
  rw [←s1, s2]
  have : (a / b - 1) * b + b - 1 = (a / b - 1) * b + (b - 1) := by
    exact Nat.add_sub_assoc hb ((a / b - 1) * b)
  simp [this]
  grind

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
    have r := @Nat.succ_mod_succ_eq_zero_iff a0 b0
    have (a b : Prop) (h : ¬a) : (b ↔ a) → ¬b := by exact (@iff_false_right a b h).mp
    have s := this ((a0 + 1) % (b0 + 1) = 0) (a0 % (b0 + 1) = b0)
    exact False.elim (this ((a0 + 1) % (b0 + 1) = 0) (a0 % (b0 + 1) = b0) h2 (id (Iff.symm r)) h1)
  have : (a0 + 1) % (b0 + 1) = 0 := by exact Nat.succ_mod_succ_eq_zero_iff.mpr h1
  exact absurd this h2

theorem mod_gt_right'' {b : ℕ} (a : ℕ) (hb : 0 < b) : (a - 1) % b + 1 ≤ b := by
  refine Nat.add_le_of_le_sub hb ?_
  · refine Nat.le_sub_one_of_lt ?_
    · exact mod_gt_right (a - 1) b hb

theorem mod_gt_right''' {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h1 : a % b ≠ 0) :
    (a - 1) % b + 1 < b := by
  have el : (a - 1) % b + 1 = b ∨ (a - 1) % b + 1 < b := by
    exact Nat.eq_or_lt_of_le (mod_gt_right'' a hb)
  rcases el with e|l
  · apply mod_gt_right'_mpr ha hb at e
    grind
  · exact l

theorem bitslength_eq_size (n : ℕ) : n.bits.length = n.size := by exact Nat.size_eq_bits_len n

theorem bits_of_double_eq_cons_false_and_bits (n : ℕ) (h : n > 0) :
    (2 * n).bits = false :: n.bits := by
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt h
  exact Nat.bit0_bits n this

theorem size_of_double_eq_self_add_one (n : ℕ) (h : n > 0) : (2 * n).size = n.size + 1 := by
  have h : (2 * n).bits = false :: n.bits := by
    exact bits_of_double_eq_cons_false_and_bits n h
  have t1 : (2 * n).bits.length = (false :: n.bits).length := by
    exact congrArg List.length h
  have t2 : (false :: n.bits).length = n.bits.length + 1 := by
    exact rfl
  simp [t2, bitslength_eq_size] at t1
  exact t1

example (n : ℕ) : (2 * n + 1).bits = true :: n.bits := by
  exact Nat.bit1_bits n

theorem size_of_two_mul_eq_aize_add_one (n : ℕ) (h : n > 0) :
    n.size + 1 = (n * 2).size := by
  simp [←Nat.size_eq_bits_len, Nat.mul_comm n 2, bits_of_double_eq_cons_false_and_bits n h]

theorem size_lt {a b : ℕ} (h : 0 < a) : 2 * a < b → a.size < b.size := by
  intro hg
  have s1 : (2 * a).bits = false :: a.bits := by refine Nat.bit0_bits a (by grind)
  have s2 : (false :: a.bits).length = 1 + a.bits.length := by
    exact Nat.succ_eq_one_add a.bits.length
  have s3 :(2 * a).bits.length = 1 + a.bits.length := by simp only [s1, s2]
  simp [bitslength_eq_size] at s3
  have stricten (a b c : ℕ) (h : 0 < b) : (a + b = c) → (a < c) := by
    have le := @Nat.le.intro a c b
    intro hh
    have le' := le hh
    clear le
    have tf : a < c ∨ a = c := by exact Or.symm (Nat.eq_or_lt_of_le le')
    clear le'
    rcases tf with t|f
    · expose_names ; exact t
    · expose_names
      simp [f] at hh
      have : ¬b = 0 := by exact Nat.ne_zero_of_lt h
      exact absurd hh this
  have tr1 : a.size < (2 * a).size := by
    exact stricten a.size 1 (2 * a).size (by grind) (by grind)
  have hg' : 2 * a ≤ b := by exact Nat.le_of_succ_le hg
  have tr2 : (2 * a).size ≤ b.size := by refine Nat.size_le_size hg'
  exact Nat.lt_of_lt_of_le tr1 tr2

theorem pow_two_of_size_le_self {n : ℕ} (h : 0 < n) : 2 ^ n.size ≤ 2 * n := by
  refine Nat.lt_size.mp ?_
  have s1 : (2 * n).bits = false :: n.bits := by refine Nat.bit0_bits n (by grind)
  have s2 : (false :: n.bits).length = 1 + n.bits.length := by
    exact Nat.succ_eq_one_add n.bits.length
  have s3 : (2 * n).bits.length = 1 + n.bits.length := by simp only [s1, s2]
  simp [bitslength_eq_size] at s3
  simp [s3]

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

theorem size_of_pow2_eq_self_add_one  (n : ℕ) : (2 ^ n).size = n + 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_of_pow2_eq_self_add_one n

theorem pow2_bit {n : ℕ} : (2 ^ n).bits = List.iterate (·) false n ++ [true] := by
  induction n with
  | zero => simp
  | succ n hn =>
    have s1 : 2 ^ (n + 1) = 2 * (2 ^ n) := by exact Nat.pow_succ'
    simp [s1]
    exact hn

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

@[deprecated "Use `size_add` instead of `bitslength_add`" (since := "2025-08-10")]
theorem bitslength_add {n k : ℕ} (ha : 0 < k) (hb : k < 2 ^ n) :
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

theorem size_add {n k : ℕ} (ha : 0 < k) (hb : k < 2 ^ n) : (2 ^ n + k).size = n + 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_add ha hb

@[deprecated "Use `size_add'` instead of `bitslength_add'`" (since := "2025-08-10")]
theorem bitslength_add' {n k : ℕ} (ha : 0 < k) (hb : (n + k).bits.length < n.bits.length + 1) :
    (n + k).bits.length = n.bits.length := by
  have t1 : n < n + k := by exact Nat.lt_add_of_pos_right ha
  have t2 : n.size ≤ (n + k).size := by
    refine Nat.size_le_size ?_
    grind
  simp [←bitslength_eq_size] at t2
  have le : n.bits.length < (n + k).bits.length ∨ n.bits.length = (n + k).bits.length := by
    exact Or.symm (Nat.eq_or_lt_of_le t2)
  rcases le with l|e
  · have l' : n.bits.length + 1 ≤ (n + k).bits.length := by exact l
    have l'' : ¬(n + k).bits.length < n.bits.length + 1 := by exact Nat.not_lt.mpr l
    exact absurd hb l''
  · exact id (Eq.symm e)

theorem size_add' {n k : ℕ} (ha : 0 < k) (hb : (n + k).size < n.size + 1) : (n + k).size = n.size := by
  simp [←bitslength_eq_size]
  simp [←bitslength_eq_size] at hb
  exact bitslength_add' ha hb

@[deprecated "Use `size_sub` instead of `bitslength_sub`" (since := "2025-08-10")]
theorem bitslength_sub {n k : ℕ} (h : 0 < n) (ha : 0 < k) (hb : k ≤ 2 ^ (n - 1)) :
    (2 ^ n - k).bits.length = n := by
  have p1 : 0 < n := by
    have p : 1 ≤ n := by exact h
    have t1 : (1 : ℕ).bits.length ≤ n := by
      have : (1 : ℕ).size ≤ n.size := by exact Nat.size_le_size h
      simp
      exact p
    simp at t1
    have t2 : 0 < 1 := by grind
    grind
  have r1 : 2 ^ n - 1 ≥ 2 ^ n - k := by grind
  have e1 : (2 ^ n - 1).bits.length = n := by simp [pow2_sub_one]
  have t1 : (2 ^ n - k).bits.length ≤ (2 ^ n - 1).bits.length := by
    have : 2 ^ n - k ≤ 2 ^ n - 1 := by exact r1
    have : (2 ^ n - k).size ≤ (2 ^ n - 1).size := by exact Nat.size_le_size r1
    simp [←bitslength_eq_size] at this
    exact this
  simp [e1] at t1
  clear e1 r1
  have t2 : n ≤ (2 ^ n - k).bits.length := by
    have r2 : 2 ^ n - 2 ^ (n - 1) ≤ 2 ^ n - k := by exact Nat.sub_le_sub_left hb (2 ^ n)
    have r2' : (2 ^ n - 2 ^ (n - 1)).bits.length ≤ (2 ^ n - k).bits.length := by
      have : (2 ^ n - 2 ^ (n - 1)).size ≤ (2 ^ n - k).size := by exact Nat.size_le_size r2
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
      have : (2 ^ n - 2 ^ (n - 1)).size = (2 ^ (n - 1)).size := by exact congrArg Nat.size e2
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
  exact Nat.le_antisymm t1 t2

theorem size_sub {n k : ℕ} (h : 0 < n) (ha : 0 < k) (hb : k ≤ 2 ^ (n - 1)) :
      (2 ^ n - k).size = n := by
  simp [←bitslength_eq_size]
  exact bitslength_sub h ha hb

@[deprecated "Use `size_div` instead of `bitslength_div`" (since := "2025-08-10")]
theorem bitslength_div {n : ℕ} (h1 : 1 ≤ n) (h2 : 2 ∣ n) :
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

theorem size_div {n : ℕ} (h1 : 1 ≤ n) (h2 : 2 ∣ n) : (n / 2).size = n.size - 1 := by
  simp [←bitslength_eq_size]
  exact bitslength_div h1 h2

theorem bitslength_le_bitslength {a b : ℕ} (h : a ≤ b) : a.bits.length ≤ b.bits.length := by
  have t := Nat.size_le_size h
  simp [←bitslength_eq_size] at t
  exact t

theorem le_if_le_size {a b : ℕ} : a.size < b.size → a < b := by
  intro h1
  by_contra h2
  simp at h2
  have c1 : b.size ≤ a.size := by exact Nat.size_le_size h2
  have c2 : ¬a.size < b.size := by exact Nat.not_lt.mpr c1
  exact absurd h1 c2

theorem size_limit {n : ℕ} (h : 0 < n) : (n + 1).size = n.size ∨ (n + 1).size = n.size + 1 := by
  have s1 : n.size ≤ (n + 1).size := by exact Nat.size_le_size (Nat.le_add_right n 1)
  have s2 : (n + 1).size ≤ n.size + 1 := by
    have t1 : (2 * n).size = n.size + 1 := by exact size_of_double_eq_self_add_one n h
    have t2 : n + 1 ≤ 2 * n := by exact add_one_le_two_mul h
    have t2' : (n + 1).size ≤ (2 * n).size := by exact Nat.size_le_size t2
    simp [t1] at t2'
    exact t2'
  by_contra h'
  push_neg at h'
  rcases h' with ⟨a, b⟩
  have c1 : n.size < (n + 1).size := by exact Nat.lt_of_le_of_ne s1 (id (Ne.symm a))
  have c2 : (n + 1).size < n.size + 1 := by exact Nat.lt_of_le_of_ne s2 b
  have c2' : (n + 1).size ≤ n.size  := by exact Nat.le_of_lt_succ c2
  have c2'' : ¬(n + 1).size > n.size := by exact Nat.not_lt.mpr c2'
  exact absurd c1 c2''

theorem pow2_is_minimum (k : ℕ) : ∀ n < 2 ^ k, n.size ≤ k := by
  intro n hn
  have t1 : n.size ≤ (2 ^ k).size := by exact Nat.size_le_size (Nat.le_of_succ_le hn)
  have t2 : (2 ^ k).size = k + 1 := by exact size_of_pow2_eq_self_add_one k
  simp [t2] at t1
  exact Nat.size_le.mpr hn

theorem n_ge_subenvelope {n: ℕ} (h : 1 ≤ n) : n ≥ 2 ^ (n.size - 1) := by
  have tf : 1 = n ∨ 1 < n := by exact Nat.eq_or_lt_of_le h
  rcases tf with t|f
  · simp [←t]
  · have n2 : (2 : ℕ).size = 2 := by simp [Nat.size, Nat.binaryRec]
    have h1 : 2 ≤ n := by exact f
    have h2 : 2 ≤ n.size := by
      have t1 : (2 : ℕ).size ≤ n.size := by exact Nat.size_le_size f
      simp [n2] at t1
      exact t1
    have : n > 2 ^ (n.size - 1) - 1 := by
      have : n.size > (2 ^ (n.size - 1) - 1).size := by
        have : (2 ^ (n.size - 1) - 1).size = n.size - 1 := by
          refine size_sub ?_ (by grind)  ?_
          · exact Nat.zero_lt_sub_of_lt h2
          · have : 0 ≤ n.size - 1 - 1 := by
              have t1 : (2 : ℕ).size - 1 - 1 ≤ n.size - 1 - 1 := by
                have : (2 : ℕ).size - 1 ≤ n.size - 1 := by
                  refine Nat.sub_le_sub_right ?_ 1
                  · simp [n2] ; exact h2
                exact Nat.sub_le_sub_right this 1
              simp
            exact Nat.one_le_two_pow
        simp [this]
        exact Nat.zero_lt_of_lt h2
      exact le_if_le_size this
    exact Nat.le_of_pred_lt this

theorem pow2size_has_upper_bound : ∀ n > 0, 2 ^ n.size ≤ 2 * n := by
  exact fun n a ↦ pow_two_of_size_le_self a

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

@[simp]
theorem trailing_zeros_prop2 :
    ∀ n > 1, n = 2 ^ (n.size - 1) → trailing_zeros n = trailing_zeros (n - 2 ^ (n.size - 2)) + 1 := by
  intro n hn1 hn2
  have n2 : 2 ≤ n.size := by
    have t1 : (2 : ℕ).size ≤ n.size := by exact Nat.size_le_size hn1
    have t2 : (2 : ℕ).size = 2 := by simp [Nat.size, Nat.binaryRec]
    exact le_of_eq_of_le (id (Eq.symm t2)) t1
  have t1 : trailing_zeros n = n.size - 1 := by
    nth_rw 1 [hn2]
    exact trailing_zeros_of_envelope (n.size - 1)
  have t2 : n - 2 ^ (n.size - 2) = 2 ^ (n.size - 2) := by
    nth_rw 1 [hn2]
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
          · exact Nat.zero_lt_succ n
          · exact Nat.one_pos
          · exact Nat.one_le_two_pow
        simp [t1] at h
        have zp : n = 0 ∨ ¬n = 0 := by exact Or.symm (ne_or_eq n 0)
        rcases zp with z|p
        · simp [z] at *
        · have even : 2 ∣ 2 ^ n := by exact Dvd.dvd.pow (by grind) p
          have odd : ¬2 ∣ 2 ^ (n + 1) := by
            simp [←h] at even
            refine Nat.two_dvd_ne_zero.mpr ?_
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

theorem parity_unmatch {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2 ^ a + 1 = 2 ^ b) : false := by
  have two_pow_a_is_even : 2 ∣ 2 ^ a := by exact dvd_pow_self 2 (Nat.ne_zero_of_lt ha)
  have even : 2 ∣ 2 ^ a + 1 := by
    simp [h]
    exact dvd_pow (by grind) (Nat.ne_zero_of_lt hb)
  have odd : ¬2 ∣ 2 ^ a + 1 := by
    refine Odd.not_two_dvd_nat ?_
    · refine Even.add_one ?_
      · exact (even_iff_exists_two_nsmul (2 ^ a)).mpr two_pow_a_is_even
  exact absurd even odd

-- TODO: no need to induction
theorem trailing_zeros_prop5 : ∀ n : ℕ, trailing_zeros (2 ^ (n + 1) + 1) = 0 := by
  intro n
  induction n with
  | zero =>
    simp
    rw [trailing_zeros]
    simp [Nat.size, Nat.binaryRec]
    rw [trailing_zeros]
    simp [Nat.size]
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
        have t4 : 4 + 1 ≤ 2 ^ (n + 1 + 1) + 1 := by exact Nat.add_le_add_right t2 1
        have t5 : (4 + 1).size ≤ (2 ^ (n + 1 + 1) + 1).size := by exact Nat.size_le_size t4
        simp at t5
        nth_rw 1 [Nat.size] at t5
        simp [Nat.binaryRec] at t5
        have t6 : 2 ≤ (2 ^ (n + 1 + 1) + 1).size - 1 := by exact Nat.le_sub_one_of_lt t5
        exact Nat.zero_lt_of_lt t6
      have c := parity_unmatch sub1 sub2 h
      simp at c
    · simp
      have t1 : (2 ^ (n + 1 + 1) + 1).size = n + 1 + 1 + 1 := by
        refine size_add (by grind) ?_
        · have s1 : 2 ≤ n + 1 + 1 := by exact Nat.le_add_left 2 n
          have s2 : 2 ^ 2 ≤ 2 ^ (n + 1 + 1) := by exact Nat.pow_le_pow_right (by grind) s1
          simp at s2
          exact Nat.one_lt_two_pow' (n + 1)
      simp [t1]
      simp [trailing_zeros]

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

theorem trailing_zeros_prop7 : ∀ n : ℕ, ∀ k < 2 ^ n,
    ¬k = 0 → trailing_zeros (k + 2 ^ n) = trailing_zeros k := by
  intro n k
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k'
    intro h1
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
        have s1 : 2 ^ n + k < 2 ^ n + 2 ^ n := by exact Nat.add_lt_add_left k' (2 ^ n)
        rw [←mul_two] at s1
        have so : (2 ^ n + k).size = n + 1 := by
          have left : n + 1 ≤ (2 ^ n + k).size := by
            have : (2 ^ n).size ≤ (2 ^ n + k).size := by
              refine Nat.size_le_size ?_
              exact Nat.le_add_right (2 ^ n) k
            exact le_of_eq_of_le (id (Eq.symm n2)) this
          have right : (2 ^ n + k).size ≤ n + 1 := by
            exact pow2_is_minimum (n + 1) (2 ^ n + k) s1
          exact Eq.symm (Nat.le_antisymm left right)
        have eq_size : (2 ^ n + k).size = (2 ^ n).size := by
          refine size_add' (by grind) ?_
          · have s4 : (2 ^ n + k).size = (2 ^ n).size := by simp [so, n2]
            simp [s4]
        split
        · expose_names
          have t1 : 2 ^ n < k + 2 ^ n := by
            refine Nat.lt_add_of_pos_left ?_
            exact Nat.zero_lt_of_ne_zero h1
          have t2 : 2 ^ n = 2 ^ ((2 ^ n).size - 1) := by
            have : (2 ^ n).size = n + 1 := by exact size_of_pow2_eq_self_add_one n
            simp [this]
          nth_rw 1 [t2] at t1
          clear t2
          simp [←eq_size] at t1
          nth_rw 1 [add_comm] at t1
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

theorem trailing_zeros_prop8 : ∀ n : ℕ, ∀ k ≤ 2 ^ n,
    ∑ i ∈ range (k - 1), (trailing_zeros (2 ^ n + i + 1) + 1)
    = ∑ i ∈ range (k - 1), (trailing_zeros (      i + 1) + 1) := by
  intro n
  intro k hk
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
        have t2 : y + 1 < k     := by exact Nat.add_lt_of_lt_sub t1
        have t3 : y + 1 < 2 ^ n := by exact Nat.lt_of_lt_of_le t2 hk
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
        have t2 : y + 1 < k     := by exact Nat.add_lt_of_lt_sub t1
        have t3 : y + 1 < 2 ^ n := by exact Nat.lt_of_lt_of_le t2 hk
        exact absurd t3 h
  simp [t3]
