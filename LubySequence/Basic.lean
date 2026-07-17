module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Size
public import LubySequence.Size

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
@[expose]
public def S₂ (n : ℕ) := 2 ^ (n.succ.size - 1)
-- #eval List.range 24 |>.map S₂

/--
Monotonicity of powers of 2: if `a ≤ b`, then `2 ^ a ≤ 2 ^ b`.
-/
public theorem pow2_le_pow2 (a b : ℕ) : a ≤ b → 2 ^ a ≤ 2 ^ b := by
  exact Nat.pow_le_pow_right (by grind : 2 > 0)

/--
For positive k, S₂ k is at least 2.
-/
public theorem S₂_ge_two (k : ℕ) (h : k > 0) : S₂ k ≥ 2 := by
  simp [S₂]
  rw [(by rfl : 2 = 2 ^1)]
  apply pow2_le_pow2
  apply Nat.le_sub_of_add_le
  simp
  have : 2 ≤ (k + 1).size := by
    obtain h1|h2 : k = 1 ∨ k > 1 := by exact LE.le.eq_or_lt' h
    · simp [h1, Nat.size, Nat.binaryRec]
    · have h1 : 1 = (1 : Nat).size := by exact Eq.symm Nat.size_one
      have h2 : 2 ≤ (2 : Nat).size := by simp [Nat.size, Nat.binaryRec]
      have h3 : 2 ≤ 1 + k := by grind
      have h4 : Nat.size 2 ≤ Nat.size (k + 1) := by
        simp only [Nat.add_comm k 1]
        exact Nat.size_le_size h3
      exact Nat.le_trans h2 h4
  exact this

-- #eval List.range 50 |>.map (fun n ↦ (if n + 1 ≥ S₂ n then 1 else 0))

/--
Checks whether `n` is an "envelope" position in the Luby sequence.

An envelope is a position where the Luby sequence reaches a local maximum value.
Specifically, `n` is an envelope if `S₂ (n + 2) = n + 2`, which corresponds to
positions `n = 2^i - 2` for some `i ≥ 1`. At these positions, the Luby value
equals `2^(i-1)`, the largest power of 2 in the current segment.

For example, envelopes occur at positions 0, 2, 6, 14, 30, ... (i.e., `2^i - 2`).
-/
@[expose]
public def isEnvelope (n : ℕ) : Bool := S₂ (n + 2) = n + 2

/--
The Luby sequence, a well-founded recursive function computing `L(n)`.

The Luby sequence is defined as:
- `luby n = S₂ n` if `n` is an envelope (i.e., `isEnvelope n = true`)
- `luby n = luby (n + 1 - S₂ n)` if `n` is not an envelope

The first 16 values (indices 0-15) are: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1, ...

The sequence is used in randomized algorithms, particularly for restart strategies
in SAT solvers and other optimization problems, where it provides a balance between
short and long runs.
-/
@[expose]
public def luby (n : ℕ) : ℕ := if isEnvelope n then S₂ n else luby (n + 1 - S₂ n)
termination_by n
decreasing_by
  obtain z|k := n
  · expose_names
    simp [isEnvelope] at h
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

/--
Checks whether position `n` is at the beginning of a segment in the Luby sequence.

A segment beginning is a position where the Luby value equals 1.
The Luby sequence can be viewed as a concatenation of segments where each segment
has a length determined by the trailing zeros of the segment index.
Positions 0 and 1 are always segment beginnings. For `n ≥ 2`, a position is a
segment beginning if it is not an envelope and recursively maps to a segment
beginning after subtracting the current envelope value `S₂ n`.

Returns `true` if `n` is either 0, 1, or maps to a segment beginning after folding.
-/
@[expose]
public def isSegmentBeg (n : ℕ) : Bool := match h : n with
  | 0 => true
  | 1 => true
  | m + 1 + 1 => if isEnvelope n then false else isSegmentBeg (n + 1 - S₂ n)
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

-- #eval! isSegmentBeg 7 -- false
-- #eval! isEnvelope 0 -- false

-- #eval (isEnvelope 14, (14 + 2).size == (14 + 1).size + 1)

-- #eval isSegmentBeg 0 -- true

end Luby

-- 🧪 Test output
-- #eval List.range 24 |>.map Luby.luby
-- Output: [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1]
