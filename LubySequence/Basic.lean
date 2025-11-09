import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Size

/-!
  The Luby sequence is a sequence of natural numbers defined recursively.
  It is used in randomized algorithms and has applications in computer science.
  The sequence is defined as follows:
```
  L(k ≥ 1) = 2^(i-1)          if k = 2^i - 1 for some i ≥ 0,
           = L(k+1 - 2^(i-1)) if 2^(i-1) ≤ k ≤ 2^i - 1
```
If we want to start the sequence from 0, to make the mapping a total function:
```
  L(k ≥ 0) = 2^(i-1)          if k = 2^i - 2 for some i ≥ 0,
           = L(k+2 - 2^(i-1)) if 2^(i-1) ≤ k + 1 ≤ 2^i - 1
```
Or
```
  L(k ≥ 0) = 2^(I(k)-1)          if (k + 2) &&& (k + 1) = 0,
           = L(k+2 - 2^(I(k)-1)) otherwise
```
where
  I(n) = ⌈log₂(n+2)⌉
-/
namespace Luby

/--
Basic relation between Nat and its binary representation.
A kind of ceiling function.

This returns the envelope + 1 (zero-based indexed).
-/
def S₂ (n : ℕ) := 2 ^ (n.succ.size - 1)
#eval List.range 24 |>.map S₂

/--
Monotonicity of powers of 2: if `a ≤ b`, then `2 ^ a ≤ 2 ^ b`.
-/
theorem pow2_le_pow2 (a b : ℕ) : a ≤ b → 2 ^ a ≤ 2 ^ b := by
  exact Nat.pow_le_pow_right (by grind : 2 > 0)

/--
The function S₂ is always non-negative (trivially true for natural numbers).
-/
theorem S₂_ge_zero (n : ℕ) : S₂ n ≥ 0 := by
  simp [S₂]

/--
The S₂ function is monotonic: `S₂ n ≤ S₂ (n + 1)` for all `n ≥ 0`.
-/
theorem S₂_is_mono : ∀ n ≥ 0, S₂ n ≤ S₂ (n + 1) := by
  intro i n0
  induction i with
  | zero => simp [S₂, Nat.size, Nat.binaryRec]
  | succ a h =>
    simp at h
    dsimp [S₂, Nat.size]
    apply pow2_le_pow2
    rw [←Nat.size]
    apply fun x ↦ Nat.sub_le_sub_right x 1
    apply Nat.size_le_size
    grind

/--
For positive k, S₂ k is at least 2.
-/
theorem S₂_ge_two (k : ℕ) (h : k > 0) : S₂ k ≥ 2 := by
  simp [S₂]
  rw [(by rfl : 2 = 2 ^1)]
  apply pow2_le_pow2
  apply Nat.le_sub_of_add_le
  simp
  have : 2 ≤ (k + 1).size := by
    have h1 : k = 1 ∨ k > 1 := by exact LE.le.eq_or_lt' h
    rcases h1 with h1|h2
    · simp [h1, Nat.size, Nat.binaryRec]
    · have h1 : 1 = (1 : Nat).size := by exact Eq.symm Nat.size_one
      have h2 : 2 ≤ (2 : Nat).size := by simp [Nat.size, Nat.binaryRec]
      have h3 : 2 ≤ 1 + k := by grind
      have h4 : Nat.size 2 ≤ Nat.size (k + 1) := by
        simp only [Nat.add_comm k 1]
        exact Nat.size_le_size h3
      exact Nat.le_trans h2 h4
  exact this

#eval List.range 50 |>.map (fun n ↦ (if n + 1 ≥ S₂ n then 1 else 0))

/--
Upper bound for S₂: `S₂ n ≤ n + 1` for all natural numbers n.
-/
theorem S₂_upper_bound : ∀ n : ℕ, S₂ n ≤ n + 1 := by
  intro n
  simp [S₂]
  refine n_ge_subenvelope ?_
  exact Nat.le_add_left 1 n

/--
Powers of 2 grow faster than linear: `n + 1 ≤ 2 ^ n` for all natural numbers n.
-/
theorem power2_ge_linear (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k h =>
    have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := by omega
    rw [h2]
    have t1 : k + 1 + 1 ≤ 2 ^ k + 1 := by omega
    have t2 : 2 ^ k + 1 ≤ 2 ^ k + 2 ^ k := by
      have : 1 ≤ 2 ^ k := by omega
      exact Nat.add_le_add_iff_left.mpr this
    have (k : ℕ) : k + k = k * 2 := by exact Eq.symm (Nat.mul_two k)
    rw [this] at t2
    exact Nat.le_trans t1 t2

#eval List.range 24 |>.map (fun k ↦ S₂ k == k)
#eval List.range 24 |>.map (fun k ↦ S₂ (k + 2) == k + 2)

def is_envelope (n : ℕ) : Bool := S₂ (n + 2) = n + 2

-- Well-founded version of the Luby sequence
def luby (n : ℕ) : ℕ := if is_envelope n then S₂ n else luby (n + 1 - S₂ n)
termination_by n
decreasing_by
  rcases n with z | k
  · expose_names
    simp [is_envelope] at h
    simp at *
    have : S₂ 2 = 2 := by simp [S₂, Nat.size, Nat.binaryRec]
    exact absurd this h
  · expose_names
    ring_nf at *
    simp at *
    have : 2 - S₂ (1 + k) < 1 → 2 + k - S₂ (1 + k) < 1 + k := by omega
    apply this
    have : 1 < S₂ (1 + k) → 2 - S₂ (1 + k) < 1 := by
      intro h
      have : S₂ (1 + k) ≥ 2 := by exact S₂_ge_two (1 + k) (by grind)
      grind
    apply this
    apply S₂_ge_two (1 + k) (by grind)

-- #eval S₂ 0 -- 2 = 2 -- 0
-- #eval luby 2 -- 2 = 2 -- 0

def is_segment_beg (n : ℕ) : Bool := match h : n with
  | 0 => true
  | 1 => true
  | m + 1 + 1 => if is_envelope n then false else is_segment_beg (n + 1 - S₂ n)
termination_by n
decreasing_by
  expose_names
  have decreasing : n + 1 - S₂ n < n := by
    simp [S₂]
    have t1 : n = m + 2 := by exact h
    have t2 : 0 ≤ m := by exact Nat.zero_le m
    have t2' : 2 ≤ m + 2 := by exact Nat.le_add_of_sub_le t2
    simp [←t1] at t2'
    have goal : 1 < S₂ n := by
      simp [S₂]
      have s1 : (2 + 1).size ≤ (n + 1).size := by
        refine Nat.size_le_size ?_
        exact Nat.add_le_add_right t2' 1
      have s2 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
      simp [s2] at s1
      exact Nat.sub_ne_zero_iff_lt.mpr s1
    simp only [S₂] at goal
    have : n.succ = n + 1 := by rfl
    simp only [this] at goal
    have goal1 : n + 1 < n + 2 ^ ((n + 1).size - 1) := by exact Nat.add_lt_add_left goal n
    have goal2 : n + 1 - 2 ^ ((n + 1).size - 1) < n := by
      have (a b c : Nat) (h : a ≥ c) : a < b + c → a - c < b := by
        exact Nat.sub_lt_right_of_lt_add h
      have c : n + 1 ≥ 2 ^ ((n + 1).size - 1) := by
        refine n_ge_subenvelope ?_
        exact Nat.le_add_left 1 n
      exact this (n + 1) n (2 ^ ((n + 1).size - 1)) c goal1
    exact goal2
  simp only [←h]
  exact decreasing

-- #eval! is_segment_beg 7 -- false
-- #eval! is_envelope 0 -- false

/--
If n is at the beginning of a segment, then luby n = 1.
-/
theorem luby_value_at_segment_beg (n : ℕ) : is_segment_beg n → luby n = 1 := by
  have luby0 : luby 0 = 1 := by
    rw [luby]
    simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
  have luby1 : luby 1 = 1 := by
    rw [luby]
    simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
    exact luby0
  induction n using Nat.strong_induction_on with
  | h n nh =>
    expose_names
    intro h
    rw [is_segment_beg.eq_def] at h
    split at h
    · expose_names ; exact luby0
    · expose_names ; simp [luby1]
    · expose_names
      split at h
      · contradiction
      · expose_names
        rw [luby]
        split
        · expose_names ; exact absurd h_2 h_1
        · expose_names
          simp at *
          let n := m + 1 + 1
          have np : n = value_of% n := by exact rfl
          simp [←np] at *
          simp [S₂]
          have r : n + 1 - 2 ^ ((n + 1).size - 1) < n := by
            have (a b c : Nat) (h : a ≥ c) : a < b + c → a - c < b := by
              exact Nat.sub_lt_right_of_lt_add h
            have c : n + 1 ≥ 2 ^ ((n + 1).size - 1) := by
              refine n_ge_subenvelope ?_
              exact Nat.le_add_left 1 n
            refine this (n + 1) n (2 ^ ((n + 1).size - 1)) c ?_
            have : 1 < 2 ^ ((n + 1).size - 1) := by
              have n2 : n ≥ 2 := by exact Nat.le_add_left 2 m
              have t1 : (2 + 1).size ≤ (n + 1).size := by
                refine Nat.size_le_size ?_
                exact Nat.add_le_add_right n2 1
              have t2 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
              simp [t2] at t1
              have t3 : 1 ≤ (n + 1).size - 1 := by exact Nat.le_sub_one_of_lt t1
              have t4 : 2 ≤ 2 ^ ((n + 1).size - 1) := by exact Nat.le_pow t3
              exact t4
            exact Nat.add_lt_add_left this n
          have goal := nh (n + 1 - S₂ n) r h
          exact goal

-- #eval (is_envelope 14, (14 + 2).size == (14 + 1).size + 1)

/--
Characterization of envelope property: n + 2 equals 2 ^ ((n + 2).size - 1)
if and only if n is an envelope.
-/
theorem envelope_prop1 (n : ℕ) : n + 2 = 2 ^ ((n + 2).size - 1) ↔ is_envelope n := by
  constructor
  · intro n2
    simp [is_envelope, S₂]
    rewrite (occs := .pos [1]) [n2]
    have t1 : (2 ^ ((n + 2).size - 1) + 1).size = ((n + 2).size - 1) + 1 := by
      refine size_add (by grind) ?_
      · have t1 : 2 ^ ((0 + 2).size - 1) ≤ 2 ^ ((n + 2).size - 1) := by
          refine pow2_le_pow2 ((0 + 2).size - 1) ((n + 2).size - 1) ?_
          refine Nat.sub_le_sub_right ?_ 1
          refine Nat.size_le_size ?_
          exact Nat.le_add_left (0 + 2) n
        simp at t1
        exact t1
    simp [t1]
    simp [←n2]
  · intro n2
    simp [is_envelope, S₂] at n2
    rewrite (occs := .pos [1]) [←n2]
    have sub1 (a b : ℕ) : a = b → 2 ^ a = 2 ^ b := by exact fun a_1 ↦ congrArg (HPow.hPow 2) a_1
    apply sub1
    have sub2 (a b c : ℕ) : a = b → a - c = b - c := by
      exact fun a_1 ↦ congrFun (congrArg HSub.hSub a_1) c
    apply sub2
    have cands : (n + 2 + 1).size = (n + 2).size ∨ (n + 2 + 1).size = (n + 2).size + 1 := by
      exact size_limit (n + 2)
    rcases cands with e|g
    · simp [e]
    · have t1 : (2 ^ ((n + 2 + 1).size - 1)).size = (n + 2).size := by exact congrArg Nat.size n2
      have t2 : (2 ^ ((n + 2 + 1).size - 1)).size = (n + 2 + 1).size - 1 + 1 := by
        exact Nat.size_pow
      simp [t2] at t1
      have t3 : (n + 2 + 1).size - 1 + 1 = (n + 2 + 1).size := by
        refine Nat.sub_add_cancel ?_
        have u1 : (0 + 2 + 1).size ≤ (n + 2 + 1).size := by
          refine Nat.size_le_size ?_
          exact Nat.le_add_left (0 + 2 + 1) n
        have u2 : (0 + 2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
        simp only [u2] at u1
        exact Nat.one_le_of_lt u1
      simp [t3] at t1
      exact t1

/--
Size characterization of envelopes: (n + 2).size = (n + 1).size + 1
if and only if n is an envelope.
-/
theorem envelope_prop2 (n : ℕ) : (n + 2).size = (n + 1).size + 1 ↔ is_envelope n := by
  have size2_eq_2 : (0 + 2).size = 2 := by simp [Nat.size, Nat.binaryRec]
  have n2size : 2 ≤ (n + 2).size := by
    have t1 : (0 + 2).size ≤ (n + 2).size := by
      refine Nat.size_le_size ?_
      exact Nat.le_add_left (0 + 2) n
    exact le_of_eq_of_le (id (Eq.symm size2_eq_2)) t1
  constructor
  · intro h
    have size_succ : (n + 2).size > (n + 1).size := by grind
    have range1 : n + 2 ≥ 2 ^ (n + 1).size := by exact Nat.lt_size.mp size_succ
    have range2 : n + 2 ≤ 2 ^ (n + 1).size := by
      have s1 : n + 1 ≤ 2 ^ (n + 1).size - 1 := by
        have : n + 1 < 2 ^ (n + 1).size := by
          exact Nat.lt_size_self (n + 1)
        exact Nat.le_sub_one_of_lt this
      have s2 : n + 1 + 1 ≤ 2 ^ (n + 1).size - 1 + 1 := by exact Nat.add_le_add_right s1 1
      have s3 : n + 1 + 1 = n + 2 := by grind
      have s4 : 2 ^ (n + 1).size - 1 + 1 = 2 ^ (n + 1).size := by
        refine Nat.sub_add_cancel ?_
        exact Nat.one_le_two_pow
      simp [s3, s4] at s2
      exact s2
    have : n + 2 = 2 ^ (n + 1).size := by exact Nat.le_antisymm range2 range1
    refine (envelope_prop1 n).mp ?_
    simp [h]
    exact this
  · intro h
    have : n + 2 = 2 ^ ((n + 2).size - 1) := by exact (envelope_prop1 n).mpr h
    simp [is_envelope, S₂] at h
    have : n + 1 = 2 ^ ((n + 2).size - 1) - 1 := by
      exact Eq.symm ((fun {n m} ↦ Nat.pred_eq_succ_iff.mpr) (id (Eq.symm this)))
    simp [this]
    have : (2 ^ ((n + 2).size - 1) - 1).size = (n + 2).size - 1 := by
      refine size_sub ?_ (by grind) ?_
      · exact Nat.zero_lt_sub_of_lt n2size
      · exact Nat.one_le_two_pow
    simp [this]
    have : (n + 2).size - 1 + 1 = (n + 2).size := by
      refine Nat.sub_add_cancel ?_
      exact Nat.one_le_of_lt n2size
    simp [this]

/--
Complement of envelope_prop2: (n + 2).size = (n + 1).size
if and only if n is not an envelope.
-/
theorem envelope_prop2' (n : ℕ) : (n + 2).size = (n + 1).size ↔ ¬is_envelope n := by
  constructor
  · intro h
    by_contra h1
    have t1 : (n + 2).size = (n + 1).size + 1 := by exact (envelope_prop2 n).mpr h1
    have t2 : ¬(n + 2).size = (n + 1).size := by grind
    exact absurd h t2
  · intro h
    by_contra hx
    have ep : (n + 2).size = (n + 1).size ∨ (n + 2).size = (n + 1).size + 1 := by
      exact size_limit (n + 1)
    rcases ep with e|p
    · exact absurd e hx
    · have : is_envelope n := by exact (envelope_prop2 n).mp p
      exact absurd this h

/--
Alternative envelope characterization: n + 2 equals 2 ^ ((n + 1).size)
if and only if n is an envelope.
-/
theorem envelope_prop1' (n : ℕ) : n + 2 = 2 ^ (n + 1).size ↔ is_envelope n := by
  have n2size : 2 ≤ (n + 2).size := by
    have t1 : (0 + 2).size ≤ (n + 2).size := by
      refine Nat.size_le_size ?_
      grind
    have t2 : (0 + 2).size = 2 := by simp [Nat.size, Nat.binaryRec]
    exact le_of_eq_of_le (id (Eq.symm t2)) t1
  constructor
  · intro h
    have t1 : (n + 2).size = (2 ^ (n + 1).size).size := by exact congrArg Nat.size h
    have t2 : (2 ^ (n + 1).size).size = (n + 1).size + 1 := by exact Nat.size_pow
    simp [t2] at t1
    exact (envelope_prop2 n).mp t1
  · intro h
    -- have t1 :
    have t1 : (n + 2).size = (n + 1).size + 1 := by exact (envelope_prop2 n).mpr h
    have env1 : n + 2 = 2 ^ ((n + 2).size - 1) := by
      exact (envelope_prop1 n).mpr h
    simp [is_envelope, S₂] at h
    rewrite (occs := .pos [1]) [env1] at h
    have : (2 ^ ((n + 2).size - 1) + 1).size = (n + 2).size - 1 + 1 := by
      refine size_add (by grind) ?_
      refine Nat.one_lt_pow ?_ (by grind)
      exact Nat.sub_ne_zero_iff_lt.mpr n2size
    simp [this] at h
    rewrite (occs := .pos [1]) [t1] at h
    exact id (Eq.symm h)

/--
For positive envelopes, the size property: if n > 0 and n is an envelope,
then (n + 1).size = n.size.
-/
theorem envelope_prop3 {n : ℕ} (h : 0 < n) (env : is_envelope n) : (n + 1).size = n.size := by
  have n1size : 2 ≤ (n + 1).size := by
    have t1 : (1 + 1).size ≤ (n + 1).size := by
      refine Nat.size_le_size ?_
      exact Nat.add_le_add_right h 1
    have t2 : (1 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
    exact le_of_eq_of_le (id (Eq.symm t2)) t1
  have e1 : n + 2 = 2 ^ ((n + 2).size - 1) := by exact (envelope_prop1 n).mpr env
  have e2 : (n + 2).size = (n + 1).size + 1 := by exact (envelope_prop2 n).mpr env
  have t1 : n + 1 = 2 ^ ((n + 2).size - 1) - 1 := by
    exact Eq.symm ((fun {n m} ↦ Nat.pred_eq_succ_iff.mpr) (id (Eq.symm e1)))
  have t2 : n = 2 ^ ((n + 2).size - 1) - 2 := by exact Nat.eq_sub_of_add_eq e1
  simp [e2] at t2
  have t3 : n.size = (2 ^ (n + 1).size - 2).size := by exact congrArg Nat.size t2
  have t4 : (2 ^ (n + 1).size - 2).size = (n + 1).size := by
    refine size_sub ?_ (by grind) ?_
    · exact Nat.zero_lt_of_lt n1size
    · have : 1 ≤ ((n + 1).size - 1) := by exact Nat.le_sub_one_of_lt n1size
      exact Nat.le_pow this
  simp [t4] at t3
  exact id (Eq.symm t3)

-- #eval is_segment_beg 0 -- true

/--
Key recursion property: either n + 1 is at a segment beginning,
or luby (n + 1) = 2 * luby n.
-/
theorem luby_value_not_at_segment_beg (n : ℕ) :
    is_segment_beg (n + 1) ∨ luby (n + 1) = 2 * luby n := by
  induction n using Nat.strong_induction_on with
  | h n nh =>
    have cases : is_segment_beg (n + 1) ∨ ¬is_segment_beg (n + 1) := by
      exact eq_or_ne (is_segment_beg (n + 1)) true
    rcases cases with beg|h
    · left ; exact beg
    · have luby0 : luby 0 = 1 := by
        rw [luby]
        simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
      have luby1 : luby 1 = 1 := by
        rw [luby]
        simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
        exact luby0
      have nsize1 : 1 ≤ (n + 1).size := by
        have t1 : (0 + 1).size ≤ (n + 1).size := by
          refine Nat.size_le_size ?_
          exact Nat.le_add_left (0 + 1) n
        have t2 : (0 + 1).size = 1 := by simp
        simp [t2] at t1
        exact t1
      · rewrite (occs := .pos [1]) [luby]
        split
        · expose_names;
          have tf : is_envelope n ∨ ¬is_envelope n := by exact eq_or_ne (is_envelope n) true
          rcases tf with t|f
          · rw [luby]
            have by_env1 : (n + 2).size = (n + 1).size + 1 := by
              exact (envelope_prop2 n).mpr t
            have by_env2 : (n + 3).size = (n + 2).size + 1 := by
              exact (envelope_prop2 (n + 1)).mpr h_1
            split
            · expose_names
              simp [S₂]
              have : n + 1 + 1 = n + 2 := by grind
              simp [this]
              simp [by_env1]
              have : 2 * 2 ^ ((n + 1).size - 1) = 2 ^ ((n + 1).size - 1 + 1) := by
                exact Eq.symm Nat.pow_succ'
              simp [this]
              right
              refine Eq.symm (Nat.sub_add_cancel ?_)
              exact Nat.one_le_of_lt nsize1
            · expose_names
              exact absurd t h_2
          · simp [S₂]
            rw [luby]
            split
            · expose_names ; exact absurd h_2 f
            · expose_names
              simp [S₂]
              -- 右辺のnはenvelopeになるので展開できる。計算できるはず。
              have env1_by_h_1 : n + 1 + 2 = 2 ^ (n + 1 + 1).size := by
                refine (envelope_prop1' (n + 1)).mpr h_1
              have env3_by_h_1 : (n + 1 + 1).size = (n + 1).size := by
                refine envelope_prop3 ?_ h_1
                exact Nat.zero_lt_succ n
              simp [env3_by_h_1]
              have env2 : is_envelope (n + 1 - 2 ^ ((n + 1).size - 1)) := by
                have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
                rcases cases with z|p
                · simp [z] ; simp [is_envelope, S₂]
                · have cases1 : n = 1 ∨ n > 1 := by exact LE.le.eq_or_lt' p
                  rcases cases1 with n1|nt
                  · simp [n1] at *
                    have t1 : is_envelope 0 = true := by
                      simp [is_envelope, S₂]
                    exact t1
                  · have t1 : n + 1 + 2 = 2 ^ (n + 1).size := by grind
                    have t1' : n + 1 = 2 ^ (n + 1).size - 2 := by grind
                    rewrite (occs := .pos [1]) [t1']
                    have t4 : 2 ^ (n + 1).size - 2 ^ ((n + 1).size - 1) = 2 ^ ((n + 1).size - 1) := by
                      refine Nat.two_pow_sub_two_pow_pred ?_
                      exact Nat.zero_lt_of_lt nsize1
                    have t5 : 2 ^ (n + 1).size - 2 - 2 ^ ((n + 1).size - 1) = 2 ^ (n + 1).size - 2 ^ ((n + 1).size - 1) - 2 := by
                      exact Nat.sub_right_comm (2 ^ (n + 1).size) 2 (2 ^ ((n + 1).size - 1))
                    simp [t5, t4]
                    clear t5 t4
                    simp [is_envelope, S₂]
                    have left1 : 2 ^ ((n + 1).size - 1) - 2 + 2 + 1 = 2 ^ ((n + 1).size - 1) + 1 := by
                      refine Nat.add_right_cancel_iff.mpr ?_
                      refine Nat.sub_add_cancel ?_
                      refine Nat.le_self_pow ?_ 2
                      refine Nat.sub_ne_zero_iff_lt.mpr ?_
                      have u1 : (2 + 1).size ≤ (n + 1).size := by
                        refine Nat.size_le_size ?_
                        exact Nat.add_le_add_right nt 1
                      have u2 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
                      simp [u2] at u1
                      exact u1
                    simp [left1]
                    have right : 2 ^ ((n + 1).size - 1) - 2 + 2 = 2 ^ ((n + 1).size - 1) := by grind
                    rw [right]
                    refine (Nat.pow_right_inj ?_).mpr ?_
                    grind
                    have : (2 ^ ((n + 1).size - 1) + 1).size = (n + 1).size - 1 + 1 := by
                      refine size_add (by grind) ?_
                      refine Nat.one_lt_two_pow ?_
                      refine Nat.sub_ne_zero_iff_lt.mpr ?_
                      have : n ≥ 2 := by exact nt
                      have u1 : (2 + 1).size ≤ (n + 1).size := by
                        refine Nat.size_le_size ?_
                        exact Nat.add_le_add_right nt 1
                      have u2 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
                      simp [u2] at u1
                      exact u1
                    simp [this]
              rw [luby]
              split
              · expose_names
                have cases : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
                rcases cases with n0|np
                · simp [n0, is_segment_beg]
                have n1size : 2 ≤ (n + 1).size := by
                  have t1 : (1 + 1).size ≤ (n + 1).size := by
                    refine Nat.size_le_size ?_
                    exact Nat.add_le_add_right np 1
                  have t2 : (1 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
                  simp [t2] at t1
                  exact t1
                right
                simp [S₂]
                have t1 : 2 * 2 ^ ((n + 1 - 2 ^ ((n + 1).size - 1) + 1).size - 1) = 2 ^ ((n + 1 - 2 ^ ((n + 1).size - 1) + 1).size - 1 + 1) := by
                  exact Eq.symm Nat.pow_succ'
                simp [t1]
                clear t1
                have t2 : n + 1 + 2 = 2 ^ (n + 1 + 1).size := by
                  exact (envelope_prop1' (n + 1)).mpr h_1
                simp [is_envelope, S₂] at h_1
                simp [env3_by_h_1] at t2
                have t3 : n + 1 = 2 ^ (n + 1).size - 2 := by
                  exact Eq.symm (Nat.sub_eq_of_eq_add (id (Eq.symm t2)))
                rewrite (occs := .pos [2]) [t3]
                have t4 : 2 ^ (n + 1).size - 2 ^ ((n + 1).size - 1) = 2 ^ ((n + 1).size - 1) := by
                  refine Nat.two_pow_sub_two_pow_pred ?_
                  exact Nat.zero_lt_of_lt nsize1
                have t5 : 2 ^ (n + 1).size - 2 - 2 ^ ((n + 1).size - 1) = 2 ^ (n + 1).size - 2 ^ ((n + 1).size - 1) - 2 := by
                  exact Nat.sub_right_comm (2 ^ (n + 1).size) 2 (2 ^ ((n + 1).size - 1))
                simp [t5, t4]
                have t6 : 2 ^ ((n + 1).size - 1) - 2 + 1 = 2 ^ ((n + 1).size - 1) - 1 := by grind
                simp [t6]
                clear t6 t5 t4 t3 t2
                have t7 : (2 ^ ((n + 1).size - 1) - 1).size = (n + 1).size - 1 := by
                  refine size_sub ?_ (by grind) ?_
                  · exact Nat.zero_lt_sub_of_lt n1size
                  · exact Nat.one_le_two_pow
                simp [t7]
                refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
                refine (Nat.two_le_iff (n + 1).size).mpr ?_
                exact Nat.one_lt_iff_ne_zero_and_ne_one.mp n1size
              · expose_names
                exact absurd env2 h_3
        · expose_names
          -- 右辺のlubyだけ展開して、帰納法に持ち込みたい
          rewrite (occs := .pos [2]) [luby]
          split
          · expose_names
            simp at h
            rw [is_segment_beg.eq_def] at h
            split at h
            · expose_names ; contradiction
            · expose_names
              have z : n = 0 := by exact Eq.symm ((fun {a b} ↦ Nat.succ_inj.mp) (id (Eq.symm heq)))
              simp [z] at *
            · expose_names
              split at h
              · expose_names ; exact absurd h_3 h_1
              · expose_names
                have t : is_segment_beg 0 := by simp [is_segment_beg.eq_def]
                have f1 : n + 1 + 1 - S₂ (n + 1) = 0 := by
                  simp [S₂]
                  have t1 : n + 1 + 1 = n + 2 := by grind
                  simp [t1]
                  have t2 : n + 2 = 2 ^ ((n + 2).size - 1) := by exact (envelope_prop1 n).mpr h_2
                  rewrite (occs := .pos [1]) [t2]
                  simp
                simp [f1] at h
                have f : ¬is_segment_beg 0 = true := by exact ne_true_of_eq_false h
                exact absurd t f
          · expose_names
            -- n = 0 or otherwise
            have : ¬n = 0 := by
              by_contra n0
              simp [n0] at *
              have c : is_envelope 0 := by simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
              have h_2' : ¬is_envelope 0 = true := by exact ne_true_of_eq_false h_2
              exact absurd c h_2'
            have n1 : n ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr this
            -- #eval is_envelope (1 + 1)
            have n2 : n ≥ 2 := by
              by_contra n2
              have t1 : n = 1 := by grind
              have t2 : is_envelope (1 + 1) = true := by
                simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
              rewrite (occs := .pos [1]) [←t1] at t2
              exact absurd t2 h_1
            have n1size' : 2 ≤ (n + 1).size := by
              have t1 : (1 + 1).size ≤ (n + 1).size := by
                refine Nat.size_le_size ?_
                exact Nat.add_le_add_right n1 1
              have t2 : (1 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
              simp [t2] at t1
              exact t1
            right
            have common1 : n + 1 + 1 = n + 2 := by grind
            have common2 : (n + 2).size = (n + 1).size := by exact (envelope_prop2' n).mpr h_2
            have common3 : S₂ n < n + 2 := by
              have : S₂ n ≤ n + 1 := by exact S₂_upper_bound n
              exact Nat.lt_add_one_of_le this
            have goal1 : n + 1 + 1 - S₂ (n + 1) = n + 1 - S₂ n + 1 := by
              simp [S₂, common1,common2]
              refine Nat.succ_sub ?_
              refine n_ge_subenvelope ?_
              exact Nat.le_add_left 1 n
            simp [goal1]
            have sub1 : n + 1 - S₂ n < n := by
              have t2 : n + 1 < n + S₂ n := by -- exact Nat.add_lt_add_left common4 n
                simp [S₂]
                refine Nat.sub_ne_zero_iff_lt.mpr ?_
                exact n1size'
              refine Nat.sub_lt_left_of_lt_add ?_ ?_
              exact S₂_upper_bound n
              rewrite (occs := .pos [2]) [add_comm]
              exact t2
            have sub2 : ¬is_segment_beg (n + 1 - S₂ n + 1) := by
              -- envelope sumになってないものからan envelop引いてもenvelop sumにはならない
              -- これは言えるはず。折りたたみはis_segment_begを保存する。
              rw [is_segment_beg.eq_def] at h
              split at h
              · expose_names ; contradiction
              · expose_names ; contradiction
              · expose_names
                split at h
                · expose_names ; exact absurd h_3 h_1
                · expose_names
                  simp [goal1] at h
                  exact ne_true_of_eq_false h
            have cases : is_segment_beg (n + 1 - S₂ n + 1) ∨ ¬is_segment_beg (n + 1 - S₂ n + 1) := by
              exact eq_or_ne (is_segment_beg (n + 1 - S₂ n + 1)) true
            rcases cases with term|recur
            · exact absurd term sub2
            · have goal1 := nh (n + 1 - S₂ n) sub1
              have : luby (n + 1 - S₂ n + 1) = 2 * luby (n + 1 - S₂ n) := by grind
              exact this

/--
Main property of the Luby sequence: luby n equals 1 if n is at a segment beginning,
otherwise it equals 2 * luby (n - 1).
-/
theorem luby_sequence_prop (n : ℕ) :
    luby n = if is_segment_beg n then 1 else 2 * luby (n - 1) := by
  have zp : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
  rcases zp with z|p
  · expose_names
    simp [z] at *
    rw [luby]
    simp [is_segment_beg, is_envelope, S₂, Nat.size, Nat.binaryRec]
  · expose_names
    have op' : n = 1 ∨ n > 1 := by exact LE.le.eq_or_lt' p
    rcases op' with o|p'
    · expose_names
      simp [o] at *
      have : is_segment_beg 1 = true := by simp [is_segment_beg]
      split
      · rw [luby]
        simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
        rw [luby]
        simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
      · rw [luby]
        simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
        rw [luby]
        simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
    · have tf : is_segment_beg n = true ∨ ¬is_segment_beg n = true := by
        exact eq_or_ne (is_segment_beg n) true
      rcases tf with t|f
      · split
        · expose_names ; exact luby_value_at_segment_beg n t
        · expose_names ; exact absurd t h
      · split
        · expose_names ; exact absurd h f
        · expose_names
          have t1 : is_segment_beg (n - 1 + 1) ∨ luby (n - 1 + 1) = 2 * luby (n - 1) := by
            exact luby_value_not_at_segment_beg (n - 1)
          have t2 : n - 1 + 1 = n := by exact Nat.sub_add_cancel p
          simp [t2] at t1
          have t3 : luby n = 2 * luby (n - 1) := by grind
          exact t3

end Luby

-- 🧪 Test output
#eval List.range 24 |>.map Luby.luby
-- Output: [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1]
