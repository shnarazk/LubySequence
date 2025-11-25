module

import Mathlib.Tactic
public import LubySequence.Basic
public import LubySequence.Segment
public import LubySequence.TrailingZeros
public import LubySequence.Utils

/-!
# State-based Luby Implementation

This module provides a state-based implementation of the Luby sequence that computes
Luby values in _O(1)_ time and transitions from state n to state n + 1 in _O(1)_ time.

The main idea is dividing the Luby sequence into monotonically increasing subsequences,
called *segments*. Each segment starts at 1 and doubles until reaching a peak value,
after which a new segment begins.

## Main Definitions

* `LubyState` - A state representing a position in the Luby sequence
* `LubyState.luby` - Computes the Luby value at the current state in O(1)
* `LubyState.next` - Transitions to the next state in O(1)
* `LubyState.ofNat` - Converts a natural number to a LubyState
* `LubyState.toNat` - Converts a LubyState back to a natural number

## Key Properties

* The state representation is isomorphic to natural numbers
* Segment heights are determined by trailing zeros of the segment index
* Each segment's Luby values form the sequence 1, 2, 4, ..., 2^(height-1)
-/

open Finset Nat

attribute [local simp] binaryRec default

/--
A state representation for efficiently computing Luby sequence values.
The state tracks position within the sequence using two components:
- `segIx`: The segment index (1-based), identifying which segment we're in
- `locIx`: The local index (0-based) within the current segment
-/
public structure LubyState where
  /-- Segment index (1-based): identifies which monotonic segment of the Luby sequence -/
  segIx : ℕ
  /-- Local index (0-based): position within the current segment -/
  locIx : ℕ

/--
Default instance for `LubyState`, starting at segment 1, local index 0.
-/
public instance LubyState.inst : Inhabited LubyState := ⟨1, 0⟩

/--
String representation of `LubyState` for debugging and display.
-/
instance LubyState.repl : Repr LubyState where
  reprPrec s _ := "LubyState(" ++ toString s.segIx ++ ", " ++ toString s.locIx ++ ")"

/--
The zero state, representing position 0 in the Luby sequence.
This is the starting state with segment index 1 and local index 0.
-/
@[expose, simp]
public def LubyState.zero := (default : LubyState)

-- #check LubyState.zero
-- #eval LubyState.zero

/--
Computes the Luby sequence value at the current state in O(1) time.
The value is `2^locIx`, since within each segment the values are 1, 2, 4, ..., 2^(height-1).
-/
@[expose]
public def LubyState.luby (self : LubyState) : ℕ := 2 ^ self.locIx

/--
Returns the height (number of elements) of the current segment.
Segment height equals `trailing_zeros(segIx) + 1`, which determines
how many times the Luby value doubles before starting a new segment.
-/
@[expose]
public def LubyState.segment_height (self : LubyState) : ℕ := trailing_zeros self.segIx + 1

/--
Returns true if this state is at the beginning of a segment (locIx = 0).
At segment beginnings, the Luby value is always 1.
-/
@[expose]
public def LubyState.is_segment_beg (self : LubyState) : Bool := self.locIx = 0

/--
Returns true if this state is at the end of a segment.
At segment ends, the Luby value reaches its peak of 2^(height-1),
and the next transition will start a new segment.
-/
@[expose]
public def LubyState.is_segment_end (self : LubyState) : Bool := self.locIx.succ = self.segment_height

/--
Transitions to the next state(s) in the Luby sequence.
- If at segment end, moves to the beginning of the next segment
- Otherwise, increments the local index within the current segment

The optional `repeating` parameter allows advancing multiple steps at once.
-/
@[expose, simp]
public def LubyState.next (self : LubyState) (repeating : ℕ := 1) : LubyState :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let li := self.next r
    if li.is_segment_end
    then LubyState.mk li.segIx.succ 0
    else LubyState.mk li.segIx li.locIx.succ

-- #eval LubyState.zero.next 2
-- #eval scanList (·.next) LubyState.zero 24 |>.map (·.luby)
-- #eval scanList (·.next) LubyState.zero 24 |>.map (fun i ↦ (i.segIx, i.locIx, i.segment_height, i.luby))
-- #eval LubyState.zero.next 24 |>.luby


namespace LubyState

/--
The next state is never equal to the current state, ensuring progress.
This shows that the state transition function is divergent (always makes progress).
-/
theorem is_divergent (li : LubyState) : ¬li.next = li := by
  by_contra! x
  simp at x
  by_cases h : li.locIx + 1 = li.segment_height <;> grind

/--
The segment index is non-decreasing: moving to the next state never decreases segIx.
-/
theorem segIx_is_increasing : ∀ li : LubyState, li.next.segIx ≥ li.segIx := by
  intro li
  simp [is_segment_end]
  by_cases h : li.locIx + 1 = li.segment_height
  <;> simp [h]

/--
The segment index is monotone: for n' ≥ n, (zero.next n').segIx ≥ (zero.next n).segIx.
-/
theorem segIx_is_mono (n : ℕ) : ∀ n' ≥ n, (zero.next n').segIx ≥ (zero.next n).segIx := by
  let cn := (zero.next n).segIx
  have cp : cn = value_of% cn := rfl
  intro n' np
  let d := n' - n
  have dp : d = value_of% d := rfl
  have dp' : n' = n + d := by exact Eq.symm (add_sub_of_le np)
  simp [dp']
  induction d with
  | zero => simp
  | succ d dq =>
    have a1 : zero.next (n + d + 1) = (zero.next (n + d)).next := by exact rfl
    have a2 : (zero.next (n + d)).next.segIx ≥ (zero.next (n + d)).segIx := by
      exact segIx_is_increasing (zero.next (n + d))
    simp at a2
    exact le_trans dq a2

/--
The segment index is always at least 1.
-/
theorem segId_ge_one : ∀ n : ℕ, (zero.next n).segIx ≥ 1 := by
  intro n
  exact (segIx_is_mono 0 n (Nat.zero_le n))

/--
Applying next 0 times returns the original state.
-/
theorem next0 (a : LubyState) : a.next 0 = a := by simp

/--
The next function preserves equality of states.
-/
theorem congr (a b : LubyState) (h : a = b) : a.next = b.next := by
  exact congrFun (congrArg (@next) h) 1

/--
n = 0 if and only if (zero.next n).segIx = 1.
This characterizes the initial state.
-/
theorem segId0 {n : ℕ} : n = 0 ↔ (zero.next n).segIx = 1 := by
  constructor
  · intro h ; rw [h] ; exact rfl
  · intro h
    by_contra x
    have base1 : (zero.next 1).segIx = 2 := by
      simp [is_segment_end, default, segment_height]
    have np : n ≥ 1 := by exact one_le_iff_ne_zero.mpr x
    have : (zero.next n).segIx ≥ 2 := by
      have sub : (zero.next n).segIx ≥ (zero.next 1).segIx := by exact segIx_is_mono 1 n np
      simp [default, is_segment_end, segment_height] at sub
      exact sub
    grind

/--
The next function is associative: (li.next n).next = li.next (n + 1).
-/
theorem next_assoc (li : LubyState) : ∀ n : ℕ, (li.next n).next = li.next (n + 1) := by
  intro n
  induction n with
  | zero => dsimp [next]
  | succ n hi =>
    rewrite (occs := .pos [3]) [next]
    by_cases h : (li.next (n + 1)).locIx.succ = (li.next (n + 1)).segment_height
    <;> simp [is_segment_end]

/--
Convert a natural number to a LubyState.
-/
@[expose]
public def ofNat (n : ℕ) : LubyState := zero.next n

/--
ofNat distributes over addition: ofNat (a + b) = (ofNat a).next b.
-/
theorem ofNat_dist (a b : ℕ) : ofNat (a + b) = (ofNat a).next b := by
  induction b with
  | zero => simp
  | succ b hb =>
    have t1 : a + (b + 1) = a + b + 1 := by grind
    simp [t1]
    have t2 : ofNat (a + b + 1) = (ofNat (a + b)).next := by exact rfl
    simp [t2, hb]

/--
An auxiliary function used to define segment properties.
Maps a natural number to a related quantity based on its successor's binary size.
-/
def S₁ (n: ℕ) : ℕ := n.succ.size.pred

-- #eval List.range 24 |>.map (fun k ↦ S₁ k)
-- #eval List.range 24 |>.map (fun k ↦ Luby.S₂ k)
-- #eval List.range 24 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

/--
Computes the cumulative sum of segment heights up to segment `n`.
This gives the index of the last element of segment `n - 1` (or 0 for segment 0).
-/
def segIdToLastIndex (n : ℕ) : ℕ := match n with
  | 0     => 0
  | m + 1 => trailing_zeros n + 1 + segIdToLastIndex m

/--
Converts a `LubyState` back to the corresponding natural number index.
The result is the cumulative segment height sum plus the local index.
-/
def toNat (self : LubyState) : ℕ := match self.segIx with
  | 0 => 0
  | n + 1 => segIdToLastIndex n + self.locIx

-- #eval scanList (·.next) zero 24 |>.map (·.toNat)

/--
The toNat and ofNat functions are inverses: (ofNat n).toNat = n for all n.
This proves that the state-based representation is isomorphic to natural numbers.
-/
theorem is_iso : ∀ n : ℕ, (ofNat n).toNat = n := by
  intro n
  change (zero.next n).toNat = n
  induction n with
  | zero => simp [toNat, segIdToLastIndex, default]
  | succ n hn =>
    simp only [toNat] at *
    split at hn
    · simp [←hn] at *
    · expose_names
      split
      · next a b =>
        have c := segId_ge_one (n + 1)
        have c' : ¬(zero.next (n + 1)).segIx = 0 := by exact ne_zero_of_lt c
        exact absurd b c'
      · expose_names
        have : (zero.next n).segIx - 1 = r := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq)))
        simp only [←this] at *
        clear this
        have : (zero.next (n + 1)).segIx - 1 = r_1 := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq_1)))
        simp [←this] at *
        clear this heq heq_1
        let c := (zero.next n).segIx
        have pc : c = value_of% c := rfl
        let s := (zero.next n).locIx
        have ps : s = value_of% s := rfl
        split
        · expose_names
          simp [is_segment_end] at h
          rw [segIdToLastIndex.eq_def]
          cases cp : c with
          | zero =>
            simp [cp] at *
            have c1 := segId_ge_one n
            have c2 : ¬0 = (zero.next n).segIx := by exact Nat.ne_of_lt c1
            exact absurd pc c2
          | succ m =>
            split
            · expose_names
              simp at heq
              simp [heq] at pc
              simp [pc] at cp
            · have h' := Eq.symm h
              simp [segment_height] at h'
              grind
        · grind

/--
Applying next increases toNat by 1: (ofNat n).next.toNat = n + 1.
-/
theorem next_is_succ : ∀ n : ℕ, (ofNat n).next.toNat = n + 1 := by
  intro n
  calc
    (ofNat n).next.toNat = (zero.next n).next.toNat := by exact rfl
    _ = (zero.next (n + 1)).toNat := by exact rfl
    _ = n + 1 := by exact is_iso (n + 1)

-- #eval List.range 28 |>.map (fun n ↦ ((ofNat n).luby, Luby.luby n))

instance : Coe ℕ LubyState where coe n := ofNat n

/--
If n is at a segment end, then n+1 is at a segment beginning.
-/
theorem LubyState_segment_prop1 {n : ℕ} (h : (ofNat n).is_segment_end = true) :
    (ofNat (n + 1)).is_segment_beg = true := by
  rw [is_segment_beg]
  have p1 : ofNat (n + 1) = (ofNat n).next := by exact rfl
  simp at p1
  split at p1
  · simp at *
    have : (ofNat (n + 1)).locIx = 0 := by grind
    exact this
  · expose_names; exact absurd h h_1

/--
At the beginning of a segment, the Luby value is 1.
-/
theorem LubyState_segment_prop2 {n : ℕ} (h : is_segment_beg n) : (ofNat n).luby = 1 := by
  simp [is_segment_beg] at h
  simp [luby]
  exact h

/--
The Luby value at position n is 1 if at segment beginning, otherwise 2 * (previous Luby value).
This is the main recurrence relation for the Luby sequence.
-/
theorem LubyState_prop (n : ℕ) :
    (ofNat n).luby = if is_segment_beg n then 1 else 2 * (ofNat (n - 1)).luby := by
  have segbeg0 : Luby.is_segment_beg 0 := by simp [Luby.is_segment_beg.eq_def]
  have segbeg1 : Luby.is_segment_beg 1 := by simp [Luby.is_segment_beg.eq_def]
  have defaultenv : (default : LubyState).is_segment_end =true := by simp [is_segment_end, segment_height]
  split
  · expose_names ; exact LubyState_segment_prop2 h
  · expose_names
    have n0 : n > 0 := by
      by_contra x
      have n0 : n = 0 := by exact Nat.eq_zero_of_not_pos x
      have c : (ofNat n).is_segment_beg = true := by simp [n0, ofNat, is_segment_beg]
      exact absurd c h
    have t1 : ofNat (n - 1 + 1) = (ofNat (n - 1)).next := by exact rfl
    have t2 : n - 1 + 1 = n := by exact Nat.sub_add_cancel n0
    simp [t2] at t1
    simp [t1]
    have t3 : ¬(ofNat (n - 1)).is_segment_end = true := by
      by_contra x
      have c : (ofNat (n - 1 + 1)).is_segment_beg := by exact LubyState_segment_prop1 x
      have t1 : n - 1 + 1 = n := by grind
      simp [t1] at c
      exact absurd c h
    split <;> expose_names
    · exact absurd h_1 t3
    · simp [luby] ; exact pow_succ'

/--
Recursively finds the segment index for a given natural number position.
Parameters:
- `n`: remaining steps to process
- `segIx`: current segment index being examined
- `sum`: cumulative sum of segment heights so far
-/
def toSegIx (n segIx sum : ℕ) : ℕ :=
  let len := trailing_zeros segIx + 1
  if hn : n <= len
  then segIx
  else
    have len1 : 1 ≤ len := by exact le_add_left 1 (trailing_zeros segIx)
    have len_n : len < n := by exact gt_of_not_le hn
    have n0 : 0 < n := zero_lt_of_lt len_n
    have n_is_decreasing : n - len < n := by
      have t1 : 0 < len := by exact zero_lt_succ (trailing_zeros segIx)
      exact sub_lt n0 t1
    toSegIx (n - len) (segIx + 1) (sum + len)

/--
Computes the sum of segment heights for segments 1 through `si`.
This equals the total number of Luby sequence elements in the first `si` segments.
-/
def sumOfSegmentHeights (si : ℕ) : ℕ := ∑ i ∈ range si, (trailing_zeros (i + 1) + 1)

-- #eval List.range 17 |>.map (fun n ↦ (n, sumOfSegmentHeights n))

/--
Computes the local index within a segment for a given natural number position.
-/
def toLocIx (n : ℕ) : ℕ := n - sumOfSegmentHeights n

/--
Advances within the same segment by `d` steps.
Unlike `next`, this does not handle segment transitions and should only
be used when the result stays within the current segment.
-/
def next_in_segment (s : LubyState) (d : ℕ) : LubyState := mk s.segIx (s.locIx + d)

/--
Stepping within a segment d' steps is the same as stepping d'-1 steps then one more step.
-/
theorem next_in_segment_is_additive {s : LubyState} {d : ℕ} :
    ∀ d' < d, 0 < d' → s.next_in_segment d' = (s.next_in_segment (d' - 1)).next_in_segment 1 := by
  intro n hn hd
  simp [next_in_segment]
  simp [add_assoc]
  exact (Nat.sub_eq_iff_eq_add hd).mp rfl

/--
When staying within a segment, locIx increments by the step amount.
-/
theorem next_in_segment_increments_locIx (s : LubyState) (d : ℕ) (h : s.locIx + d < s.segment_height) :
    (s.next_in_segment d).locIx = s.locIx + d := by
  induction d with
  | zero => simp [next_in_segment]
  | succ d hd =>
    have h' : s.locIx + d < s.segment_height := by exact lt_of_succ_lt h
    have t1 : s.next_in_segment (d + 1) = (s.next_in_segment d).next_in_segment 1 := by exact rfl
    simp [t1]
    rewrite (occs := .pos [1]) [next_in_segment]
    simp [hd h']
    exact rfl

/--
When staying within a segment, next_in_segment and next produce the same result.
-/
theorem next_in_segment_is_next (s : LubyState) (d : ℕ) (h : s.locIx + d < s.segment_height) :
    next_in_segment s d = s.next d := by
  induction d with
  | zero => simp [next_in_segment]
  | succ d hd =>
    have h' : s.locIx + d < s.segment_height := by exact lt_of_succ_lt h
    have t1 : s.next_in_segment (d + 1) = (s.next_in_segment d).next_in_segment 1 := by exact rfl
    simp [t1]
    rewrite (occs := .pos [1]) [next_in_segment]
    simp [hd h']
    simp [←hd h']
    simp [is_segment_end]
    have t2 : (s.next_in_segment d).locIx = s.locIx + d := by exact rfl
    simp [t2]
    exact Nat.ne_of_lt h

/--
After traversing a complete segment starting from its beginning, we reach the next segment's beginning.
-/
theorem segment_beg_transition' : ∀ n : ℕ, (ofNat n).is_segment_beg = true →
    (ofNat (n + (ofNat n).segment_height)).is_segment_beg := by
  intro n hz
  let n' := ofNat n
  have nn : n' = value_of% n' := by exact rfl
  simp [←nn]
  have z : n'.locIx = 0 := by simp [is_segment_beg, ←nn] at hz ; exact hz
  have : n + n'.segment_height = (n + n'.segment_height - 1) + 1 := by exact rfl
  rw [this]
  replace : ofNat (n + n'.segment_height - 1 + 1) = (ofNat (n + n'.segment_height - 1)).next 1 := rfl
  simp only [this]
  replace : n + n'.segment_height - 1 = n + (n'.segment_height - 1) := by exact rfl
  simp only [this]
  replace : ofNat (n + (n'.segment_height - 1)) = (ofNat n).next (n'.segment_height - 1) := by
    exact ofNat_dist n (n'.segment_height - 1)
  simp only [this]
  replace :
      (ofNat n).next (n'.segment_height - 1) = (ofNat n).next_in_segment (n'.segment_height - 1) := by
    refine Eq.symm (next_in_segment_is_next (ofNat n) (n'.segment_height - 1) ?_)
    simp [←nn, z]
    simp [segment_height]
  simp only [this]
  simp only [←nn]
  replace : (n'.next_in_segment (n'.segment_height - 1)).locIx = n'.locIx + n'.segment_height - 1 := rfl
  simp [z] at this
  simp [this]
  split
  · expose_names ; simp [is_segment_beg]
  · expose_names
    simp [is_segment_end] at h
    rw [this] at h
    replace : (n'.next_in_segment (n'.segment_height - 1)).segment_height = n'.segment_height := rfl
    simp [this] at h
    have c : n'.segment_height - 1 + 1 = n'.segment_height := by exact this
    exact absurd c h

/--
The sum of segment heights from segment 1 to segment `b`.
This gives the index of the beginning of segment `b + 1`.
-/
def segment_height_sum (b : ℕ) : ℕ := ∑ i ∈ range b, (trailing_zeros (i + 1) + 1)

/- #eval List.range 12 |>.map (fun n ↦ (segment_height_sum n, segment_height_sum' n))
#eval List.range 7 |>.map (fun k ↦ (2 ^ k, segment_height_sum (2 ^ k), 2 ^ (k + 1) - 1))

#eval List.range 30 |>.map (fun n ↦ (
    (ofNat (∑ k < (ofNat n).segIx, (trailing_zeros k + 1) - 1)).segIx,
    (ofNat n).segIx))

#eval List.range 20 |>.map (· + 1) |>.map (fun n ↦ (
  (∑ i ∈ range       n, (trailing_zeros       i + 1)),
  (∑ i ∈ range (n - 1), (trailing_zeros (i + 1) + 1) + 1)))

#eval List.range 7 |>.map (fun k ↦
  let n := 2 ^ k
  (∑ i ∈ range n, (trailing_zeros (i + 1) + 1), 2 ^ n.size - 1))
-/

/--
For powers of 2, the sum of segment heights equals 2^(n.size) - 1.
This is a key property connecting segment heights to the binary structure.
-/
theorem segment_height_sum_pow2' : ∀ n > 0, n = 2 ^ (n.size - 1) →
    ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) = 2 ^ n.size - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h
    have cases : n = 1 ∨ 1 < n := by exact LE.le.eq_or_lt' h
    rcases cases with case1|case2
    · simp [case1]
    · intro h2
      have nsize2 : 2 ≤ n.size := by
        have u1 : (2 : ℕ).size ≤ n.size := by exact size_le_size case2
        have u2 : (2 : ℕ).size = 2 := by simp [size, binaryRec]
        simp [u2] at u1
        exact u1
      have t1 : range n = range (2 ^ (n.size - 1)) := by exact congrArg range h2
      simp [t1]
      have t2 : 2 ^ (n.size - 1) = 2 * 2 ^ (n.size - 1 - 1) := by
        exact Eq.symm (mul_pow_sub_one (sub_ne_zero_of_lt (lt_size.mpr case2)) 2)
      simp [t2]
      clear t1 t2
      rw [two_mul]
      rw [sum_range_add]
      have sub1 : 2 ^ (n.size - 1 - 1) < n := by
        have t1 : 2 ^ n.size ≤ 2 * n := by exact pow2size_has_upper_bound n (by grind)
        have t2 : 2 ^ n.size / 2 ≤ 2 * n / 2 := by exact Nat.div_le_div_right t1
        have t3 : 2 * n / 2 = n := by grind
        simp [t3] at t2
        clear t3
        have t4 : 2 ^ n.size / 2 = 2 ^ (n.size - 1) := by
          refine Nat.div_eq_of_eq_mul_right (by grind) ?_
          · have : 2 = 2 ^ 1 := by exact rfl
            rewrite (occs := .pos [2]) [this]
            exact Eq.symm (mul_pow_sub_one (by grind) (2 ^ 1))
        simp [t4] at t2
        have t5 : 2 ^ (n.size - 1 - 1) < 2 ^ (n.size - 1) := by
          exact Nat.two_pow_pred_lt_two_pow (zero_lt_sub_of_lt (lt_size.mpr case2))
        exact lt_of_lt_of_le t5 t2
      have sub2 : 2 ^ (n.size - 1 - 1) > 0 := Nat.two_pow_pos (n.size - 1 - 1)
      have sub3 : 2 ^ (n.size - 1 - 1) = 2 ^ ((2 ^ (n.size - 1 - 1)).size - 1) := by
        have : n.size - 1 - 1 = (2 ^ (n.size - 1 - 1)).size - 1 := by
          have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 - 1 + 1 := size_pow
          simp [this]
        rw (occs := .pos [1]) [this]
      have ih' := ih (2 ^ (n.size - 1 - 1)) sub1 sub2 sub3
      clear sub1 sub2 sub3
      simp [ih']
      have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 := by
        have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 - 1 + 1 := by exact size_pow
        simp [this]
        exact Nat.sub_add_cancel (le_sub_one_of_lt nsize2)
      simp [this]
      -- 最後の1個を一旦外す
      have t1 : 2 ^ (n.size - 1 - 1) = 2 ^ (n.size - 1 - 1) - 1 + 1 := by
        exact Eq.symm (Nat.sub_add_cancel Nat.one_le_two_pow)
      rewrite (occs := .pos [1]) [t1]
      rw [sum_range_succ]
      -- shift left part1
      replace : ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1), (trailing_zeros (2 ^ (n.size - 1 - 1) + x + 1) + 1) =
          ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1), (trailing_zeros (x + 1) + 1) := by
        refine trailing_zeros_prop8 (n.size - 1 - 1) (2 ^ (n.size - 1 - 1)) ?_
        exact le_refl (2 ^ (n.size - 1 - 1))
      simp [this]
      replace : 2 ^ (n.size - 1 - 1) + (2 ^ (n.size - 1 - 1) - 1) + 1 = 2 ^ (n.size - 1) := by
        have : 2 ^ (n.size - 1 - 1) + (2 ^ (n.size - 1 - 1) - 1) + 1 =
            2 ^ (n.size - 1 - 1) + 2 ^ (n.size - 1 - 1) - 1 + 1 := by
          refine add_right_cancel_iff.mpr ?_
          · exact Eq.symm (Nat.add_sub_assoc Nat.one_le_two_pow (2 ^ (n.size - 1 - 1)))
        simp [this]
        refine Eq.symm (Nat.eq_add_of_sub_eq ?_ ?_)
        · exact Nat.one_le_two_pow
        · have : 2 ^ (n.size - 1) = 2 ^ (n.size - 1 - 1) + 2 ^ (n.size - 1 - 1) := by
            have : 2 ^ (n.size - 1 - 1) + 2 ^ (n.size - 1 - 1) = 2 ^ (n.size - 1 - 1 + 1) := by
              exact Eq.symm (two_pow_succ (n.size - 1 - 1))
            simp [this]
            exact (Nat.sub_eq_iff_eq_add nsize2).mp rfl
          simp [this]
      simp [this]
      -- shift left part 2
      replace : trailing_zeros (2 ^ (n.size - 1)) = trailing_zeros (2 ^ (n.size - 1 - 1)) + 1 := by
        have s1 : trailing_zeros (2 ^ (n.size - 1)) = n.size - 1 := trailing_zeros_prop3 (n.size - 1)
        have s2 : trailing_zeros (2 ^ (n.size - 1 - 1)) = n.size - 1 - 1 := by
          exact trailing_zeros_prop3 (n.size - 1 - 1)
        simp [s1, s2]
        exact (Nat.sub_eq_iff_eq_add nsize2).mp rfl
      simp [this]
      replace :
          ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1),
            (trailing_zeros (x + 1) + 1) + (trailing_zeros (2 ^ (n.size - 1 - 1)) + 1 + 1) =
          ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1),
            (trailing_zeros (x + 1) + 1) + (trailing_zeros (2 ^ (n.size - 1 - 1)) + 1) + 1 := by
        exact rfl
      simp only [this]
      replace : (2 ^ (n.size - 1 - 1) - 1 + 1) = (2 ^ (n.size - 1 - 1)) := id (Eq.symm t1)
      rewrite (occs := .pos [2]) [←this]
      rw [←sum_range_succ (fun n ↦ trailing_zeros (n + 1) + 1) (2 ^ (n.size - 1 - 1) - 1)]
      simp [this, ih']
      replace : (2 ^ (n.size - 1 - 1)).size = n.size - 1 := by
        have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 - 1 + 1 := by exact size_pow
        simp [this]
        grind
      simp [this]
      replace : 2 ^ (n.size - 1) - 1 + 1 = 2 ^ (n.size - 1) := by grind
      simp [this]
      replace : 2 ^ (n.size - 1) - 1 + 2 ^ (n.size - 1) = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) - 1 := by
        exact Eq.symm (Nat.sub_add_comm Nat.one_le_two_pow)
      simp [this]
      replace : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) = 2 ^ n.size := by
        have : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) = 2 * 2 ^ (n.size - 1) := by
          exact Eq.symm (two_mul (2 ^ (n.size - 1)))
        simp [this]
        replace : 2 * 2 ^ (n.size - 1) = 2 ^ (n.size - 1 + 1) := by exact Eq.symm pow_succ'
        simp [this]
        exact Nat.sub_add_cancel (one_le_of_lt nsize2)
      simp [this]

/--
For powers of 2, the sum of segment heights from 1 to `b` equals `2 * b - 1`
when `b = 2^(b.size - 1)`.
-/
theorem segment_height_sum_pow2 : ∀ b : ℕ, b = 2 ^ (b.size - 1) → segment_height_sum b = 2 * b - 1 := by
  intro b b_is_pow2
  have b_ge_1 : b ≥ 1 := by
    by_contra x
    simp at x
    simp [x] at b_is_pow2
  have b.size_ge_1 : b.size ≥ 1 := by
    have : b.size ≥ (1 : ℕ).size := by exact size_le_size b_ge_1
    simp at this
    exact this
  rw [segment_height_sum]
  rw (occs := .pos [2]) [b_is_pow2]
  rw [mul_comm, ←pow_succ]
  have : b.size - 1 + 1 = b.size := by exact Nat.sub_add_cancel b.size_ge_1
  simp [this]
  exact segment_height_sum_pow2' b b_ge_1 b_is_pow2

-- #eval List.range 7 |>.map (2 ^ · - 1) |>.map (fun n ↦ (n, (ofNat (n - 1)).segment_height, n.size))

/--
For `k ≥ 0`, `segment_height_sum (2^k) = 2^(k+1) - 1`.
This connects segment structure to powers of 2.
-/
theorem segment_height_sum_is_envelope : ∀ k : ℕ, segment_height_sum (2 ^ k) = 2 ^ (k + 1) - 1 := by
  intro k
  simp [segment_height_sum]
  induction k with
  | zero => simp [trailing_zeros]
  | succ k ih =>
    have t1 : ∑ i ∈ range (2 ^ (k + 1) - 2 + 2), (trailing_zeros (i + 1) + 1) =
      ∑ i ∈ range (2 ^ (k + 1) - 2), (trailing_zeros (i + 1) + 1)
      + ∑ i ∈ range 2, (trailing_zeros (2 ^ (k + 1) - 2 + i + 1) + 1) := by
      exact sum_range_add (fun x ↦ trailing_zeros (x + 1) + 1) (2 ^ (k + 1) - 2) 2
    have t2 : 2 ^ (k + 1) - 2 + 2 = 2 ^ (k + 1) := by
      exact Nat.sub_add_cancel (le_self_pow (Ne.symm (zero_ne_add_one k)) 2)
    simp [t2] at t1
    simp [t1]
    have t3 : ∑ i ∈ range 2, (trailing_zeros (2 ^ (k + 1) - 2 + i + 1) + 1) =
        (trailing_zeros (2 ^ (k + 1) - 2 + 0 + 1) + 1) + (trailing_zeros (2 ^ (k + 1) - 2 + 1 + 1) + 1)
        := by
      exact rfl
    simp [t3]
    have t4 : 2 ^ (k + 1) - 2 + 1 = 2 ^ (k + 1) - 1 := by
      exact Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) (id (Eq.symm t2)))
    simp [t4]
    have t5 : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by exact Nat.sub_add_cancel Nat.one_le_two_pow
    simp [t5]
    have t6 : trailing_zeros (2 ^ (k + 1)) = k + 1 := by exact trailing_zeros_prop3 (k + 1)
    simp [t6]
    have t7 : trailing_zeros (2 ^ (k + 1) - 1) = 0 := by exact trailing_zeros_prop4 (k + 1)
    simp [t7]
    have zp : k = 0 ∨ k > 0 := by exact Nat.eq_zero_or_pos k
    rcases zp with z|p
    · simp [z] at *
    · have : range (2 ^ (k + 1) - 2) = range (2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2)) := by
        have t1 : 2 ^ (k + 1) = 2 ^ k + (2 ^ (k + 1) - 2 ^ k) := by grind
        have t2 : 2 ^ (k + 1) - 2 = 2 ^ k + (2 ^ (k + 1) - 2 ^ k) - 2 := by grind
        have t2' : 2 ^ (k + 1) - 2 = 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) := by
          refine Nat.sub_eq_of_eq_add ?_
          have : 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) + 2 = 2 ^ k + 2 ^ (k + 1) - 2 ^ k - 2 + 2 := by
            have : 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) = 2 ^ k + 2 ^ (k + 1) - 2 ^ k - 2 := by
              have : 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) = 2 ^ k + 2 ^ (k + 1) - 2 ^ k - 2 := by
                have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by exact two_pow_succ k
                simp [this]
                have : 2 ^ k + (2 ^ k - 2) = 2 ^ k + 2 ^ k - 2 := by
                  exact Eq.symm (Nat.add_sub_assoc (le_pow p) (2 ^ k))
                simp [this]
              simp [this]
            exact Nat.add_left_inj.mpr this
          simp [this]
          grind
        rw [←t2']
      simp [this]
      simp [sum_range_add]
      simp [ih]
      have t8 : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
        refine Nat.sub_eq_of_eq_add ?_
        · rw [←mul_two]
          exact rfl
      simp [t8]
      have t9 : ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (2 ^ k + i + 1) + 1)
          = ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (i + 1) + 1) := by
        exact trailing_zeros_prop8 k (2 ^ k - 1) (sub_le (2 ^ k) 1)
      simp [t9]
      have t10 : ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (i + 1) + 1) + (trailing_zeros (2 ^ k - 2 + 1) + 1) := by
        have s1 : 2 ^ k - 1 = 2 ^ k - 1 - 1 + 1 := by
          refine Eq.symm (Nat.sub_add_cancel ?_)
          · exact le_sub_one_of_lt (Nat.one_lt_two_pow (ne_zero_of_lt p))
        rewrite (occs := .pos [1]) [s1]
        have s2 : 2 ^ k - 1 - 1 = 2 ^ k - 2 := rfl
        rewrite (occs := .pos [1]) [s2]
        rw [sum_range_succ]
      have t10' : ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) - (trailing_zeros (2 ^ k - 2 + 1) + 1) := by
        exact Nat.eq_sub_of_add_eq (id (Eq.symm t10))
      simp [t10']
      clear t10' t10 t9 t8 t7 t6 t5 t4 t3 t2 t1 this
      have t1 : trailing_zeros (2 ^ k - 2 + 1) + 1 = 1 := by
        have : 2 ^ k - 2 + 1 = 2 ^ k - 1 := by
          have s1 : 2 ^ k - 2 + 2 = 2 ^ k := Nat.sub_add_cancel (le_pow p)
          have s2 : 2 = 1 + 1 := rfl
          rewrite (occs := .pos [3]) [s2] at s1
          have s3 : 2 ^ k - 2 + (1 + 1) = 2 ^ k - 2 + 1 + 1 := by exact rfl
          simp [s3] at s1
          exact Eq.symm ((fun {n m} ↦ pred_eq_succ_iff.mpr) (id (Eq.symm s1)))
        simp [this]
        exact trailing_zeros_prop4 k
      simp [t1]
      have t2 : ∑ i ∈ range (2 ^ k), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) + (trailing_zeros (2 ^ k - 1 + 1) + 1) := by
        have s1 : 2 ^ k = 2 ^ k - 1 + 1 := Eq.symm (Nat.sub_add_cancel Nat.one_le_two_pow)
        rewrite (occs := .pos [1]) [s1]
        rw [sum_range_succ]
      have t2' : ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k), (trailing_zeros (i + 1) + 1) - (trailing_zeros (2 ^ k - 1 + 1) + 1) := by
        exact Nat.eq_sub_of_add_eq (id (Eq.symm t2))
      simp [t2', ih]
      have t3 : trailing_zeros (2 ^ k - 1 + 1) = k := by
        have : 2 ^ k - 1 + 1 = 2 ^ k := by exact Nat.sub_add_cancel Nat.one_le_two_pow
        simp [this]
        exact trailing_zeros_prop3 k
      simp [t3]
      rw [add_comm]
      have t4 : 2 ^ (k + 1) - 1 + (2 ^ (k + 1) - 1 - (k + 1) - 1)
          = 2 ^ (k + 1) + (2 ^ (k + 1) - 1 - (k + 1) - 1) - 1 := by
        exact Eq.symm (Nat.sub_add_comm (by grind))
      simp [t4]
      let x := 1 + (k + 1) + 1
      have hx : x = value_of% x := rfl
      have base1 : (k + 1) + 2 ≤ 2 ^ (k + 1) := by
        let x := k - 1
        have hx : x = value_of% x := rfl
        have hx' : x + 1 = k := Nat.sub_add_cancel p
        simp [←hx']
        induction x with
        | zero => simp
        | succ x hx =>
          have s1 : x + 1 + 1 + 1 + 2 = 1 + (x + 1 + 1 + 2) := by grind
          simp [s1]
          have s2 : 1 < 2 ^ (x + 1 + 1) := by exact lt_of_add_left_lt hx
          have s3 : 2 ^ (x + 1 + 1 + 1) = 2 ^ (x + 1 + 1) + 2 ^ (x + 1 + 1) := by
            exact two_pow_succ (x + 2)
          simp [s3]
          exact Nat.add_le_add Nat.one_le_two_pow hx
      have t5 : 2 ^ (k + 1) - 1 - (k + 1) - 1 = 2 ^ (k + 1) - x := by
        simp [hx]
        refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
        · refine le_sub_of_add_le ?_
          · refine add_le_of_le_sub ?_ ?_
            · exact le_sub_one_of_lt Nat.lt_two_pow_self
            · exact le_sub_of_add_le (one_add_le_iff.mpr (lt_sub_of_add_lt base1))
        · have : 2 ^ (k + 1) - (1 + (k + 1) + 1) + 1 = 2 ^ (k + 1) - (k + 1) - 1 := by
            have : 2 ^ (k + 1) - (1 + (k + 1) + 1) + 1 = 2 ^ (k + 1) + 1 - (1 + (k + 1) + 1) := by
              refine Eq.symm (Nat.sub_add_comm ?_)
              refine add_le_of_le_sub ?_ ?_
              · exact Nat.one_le_two_pow
              · have s1 : (k + 1) + 1 + 1 ≤ 2 ^ (k + 1) := by exact base1
                have s2 : 1 + (k + 1) + 1 = k + 1 + 1 + 1 := by exact Eq.symm (add_comm (k + 1 + 1) 1)
                simp [←s2] at s1
                exact le_sub_one_of_lt s1
            simp [this]
            exact Simproc.sub_add_eq_comm (2 ^ (k + 1)) 1 (k + 1)
          simp [this]
          exact Nat.sub_right_comm (2 ^ (k + 1)) 1 (k + 1)
      simp [t5]
      have t6 : 2 ^ (k + 1) + (2 ^ (k + 1) - x) = 2 ^ (k + 1) + 2 ^ (k + 1) - x := by
        refine Eq.symm (Nat.add_sub_assoc ?_ (2 ^ (k + 1)))
        · simp [hx] ; rw [add_comm, ←add_assoc] ; simp [add_comm] ; exact base1
      simp [t6]
      have t7 : 2 ^ (k + 1) + 2 ^ (k + 1) = 2 ^ (k + 1 + 1) := by exact Eq.symm (two_pow_succ (k + 1))
      simp [t7, hx]
      have t8 : 1 + (k + 1 + 1) = k + 1 + 1 + 1 := by exact add_comm 1 (k + 1 + 1)
      simp [t8]
      let y := k + 1 + 1 + 1
      have hy : y = value_of% y := by exact rfl
      have t9 : 1 + (k + 1) + 1 = y := by grind
      simp [t9 , ←hy]
      have t10 : 2 ^ (k + 1 + 1) - y - 1 = 2 ^ (k + 1 + 1) - (y + 1) := by exact rfl
      simp [t10]
      simp [hy]
      clear t10 t9 t8 t7 t6 t5 t4 t3 t2' t2 t1 hy x y hx
      rw [add_comm]
      have cond {k : ℕ} (h : 0 < k) : 2 ^ (k + 1 + 1) ≥ (k + 1 + 1 + 1 + 1) := by
        induction k with
        | zero => simp
        | succ k ih =>
          expose_names
          clear ih_1
          have two_cases : k = 0 ∨ ¬k = 0 := by exact Or.symm (ne_or_eq k 0)
          rcases two_cases with k0|kp
          · simp [k0]
          · have kp' : 0 < k := by exact zero_lt_of_ne_zero kp
            have t1 : 2 ^ (k + 1 + 1 + 1) = 2 * 2 ^ (k + 1 + 1) := by exact pow_succ'
            rw [mul_comm, mul_two] at t1
            simp [t1]
            exact Nat.add_le_add (ih kp') Nat.one_le_two_pow
      have : 2 ^ (k + 1 + 1) - (k + 1 + 1 + 1 + 1) + (k + 1 + 1 + 1)
          = 2 ^ (k + 1 + 1) + (k + 1 + 1 + 1) - (k + 1 + 1 + 1 + 1) := by
        exact Eq.symm (Nat.sub_add_comm (cond p))
      simp [this]
      grind

section WIP
-- t20250910 よりも
-- - envelope hightが2 ^ n.size - 1 でのsegment_hightと等しいこと
-- をいう方が簡単なのでは。
-- - そもそもsegmentの左右対称性が何も言えてない。

-- #CURRENT-TASK

-- #eval List.range 9 |>.map (2 ^ · - 1) |>.map (fun n ↦ (n.size - 1, (ofNat (n - 1)).locIx))

/--
Work in progress: For envelopes, the local index equals size - 1.
これの前に漸化式が必要なのでは? あるいは左右対称性が必要なのでは?
でもそれを証明するにはenvelopeでの定数化が先に必要なのでは?
-/
theorem t20250919 : ∀ n : ℕ, n + 1 = 2 ^ n.size → (ofNat (n - 1)).locIx = n.size - 1 := by
  intro n n1_is_pow2
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n = 0
    · simp [zero, ofNat, default]
    · rename' zero => n_ge_1
      replace n_ge_1 : n ≥ 1 := by exact one_le_iff_ne_zero.mpr n_ge_1
      replace n_ge_1 : n = 1 ∨ n > 1 := by exact LE.le.eq_or_lt' n_ge_1
      rcases n_ge_1 with eq|n_ge_2
      · simp [eq, ofNat]
      · replace n_ge_2 : n ≥ 2 := n_ge_2
        have nsize_ge_2 : n.size ≥ 2 := by
          have : n.size ≥ (2 : ℕ).size := by exact size_le_size n_ge_2
          simp [size2_eq_2] at this
          exact this
        let n' := 2 ^ (n.size - 1) - 1
        have n'_def : n' = value_of% n' := by exact rfl
        have n'_lt_n : n' < n := by
          have : 2 ^ (n.size - 1) ≤ n := n_lower (zero_lt_of_lt n_ge_2)
          replace : 2 ^ (n.size - 1) - 1 < n := sub_one_lt_of_le (Nat.two_pow_pos (n.size - 1)) this
          simp [←n'_def] at this
          exact this
        have n'1_is_pow2 : n' + 1 = 2 ^ n'.size := by
          have : n'.size = n.size - 1 := by
            have : n'.size = (2 ^ (n.size - 1) - 1).size := rfl
            have aux : (2 ^ (n.size - 1) - 1).size = n.size - 1 := by
              refine size_sub ?_ ?_ ?_
              · exact zero_lt_sub_of_lt nsize_ge_2
              · exact Nat.one_pos
              · exact Nat.one_le_two_pow
            simp [aux] at this
            exact this
          simp [←this] at n'_def
          replace n'_def : n' + 1 = 2 ^ n'.size := by
            exact Eq.symm (Nat.eq_add_of_sub_eq (Nat.one_le_two_pow) (id (Eq.symm n'_def)))
          exact n'_def
        have ih' := ih n' n'_lt_n n'1_is_pow2
        rw [ofNat]
        sorry -- ???


-- #eval List.range 7 |>.map (2 ^ · - 1) |>.map (fun n ↦ (n, (ofNat (n - 1)).segIx, 2 ^ (n.size - 1)))
/- #eval List.range 64
    |>.filter (fun n ↦ 0 < n && n == 2 ^ n.size - 2)
    |>.map (fun n ↦ (n, (ofNat n).segIx, 2 * (ofNat (n - (2 ^ (n.size - 1)))).segIx, 2 ^ (n.size - 1)))
-/

/--
Work in progress: Segment index doubling property at envelope boundaries.
-/
theorem t20250910 : ∀ n > 0 , n = 2 ^ n.size - 2 →
    (ofNat n).segIx = 2 * (ofNat (n - (2 ^ (n.size - 1)))).segIx := by
  intro n hn1 hn2
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have zp : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
    rcases zp with z|p
    · simp [z] at *
    · let i := n - 1
      have pi : i = value_of% i := by exact rfl
      have n_to_i : n = i + 1 := by exact (Nat.sub_eq_iff_eq_add hn1).mp pi
      have i1 : i ≥ 1 := by
        by_contra i0
        simp at i0
        simp [i0] at *
        simp [n_to_i] at hn2
      simp [n_to_i] at *
      have t1 : i + 1 - 2 ^ ((i + 1).size - 1) = 2 ^ ((i + 1).size - 1) - 2 := by
        rewrite (occs := .pos [1]) [hn2]
        have : (i + 1).size = (i + 1).size - 1 + 1 := by
          refine (Nat.sub_eq_iff_eq_add ?_).mp rfl
          · have r1 : 0 + 1 ≤ i + 1 := by exact Nat.le_add_left (0 + 1) i
            have r2 : (0 + 1).size ≤ (i + 1).size := by exact size_le_size r1
            have r3 : (0 + 1).size = 1 := by simp [size]
            simp [r3] at r2
            exact r2
        rewrite (occs := .pos [1]) [this]
        replace : 2 ^ ((i + 1).size - 1 + 1) = 2 * 2 ^ ((i + 1).size - 1) := Nat.pow_succ'
        simp [this]
        rw [mul_comm, mul_two]
        have :
            2 ^ ((i + 1).size - 1) + 2 ^ ((i + 1).size - 1) - 2 - 2 ^ ((i + 1).size - 1) =
            2 ^ ((i + 1).size - 1) + 2 ^ ((i + 1).size - 1) - 2 ^ ((i + 1).size - 1) - 2 := by
          exact Nat.sub_right_comm
              (2 ^ ((i + 1).size - 1) + 2 ^ ((i + 1).size - 1))
              2
              (2 ^ ((i + 1).size - 1))
        simp [this]
      rewrite (occs := .pos [1]) [t1]
      --
      sorry

-- #eval List.range 32 |>.map (fun n ↦ ((∑ k ∈ Iio (ofNat n).segIx, (trailing_zeros k + 1) - 1), n))
/- #eval List.range 32 |>.map (fun n ↦
      ((ofNat (∑ k ∈ Iio (ofNat n).segIx, (trailing_zeros k + 1) - 1)).segIx, (ofNat n).segIx))
-/

/--
Work in progress: Sum of index in segment corresponds to segment index.
-/
theorem locIx_eq_0_at_segment_beg : ∀ n : ℕ,
    (ofNat (∑ k ∈ range (ofNat n).segIx, (trailing_zeros k + 1) - 1)).locIx = 0 := by
  intro n
  induction n with
  | zero => simp [range, ofNat, next]
  | succ n ih =>
    have : ∑ k ∈ range ((ofNat (n + 1)).segIx - 1 + 1), (trailing_zeros k + 1) =
        ∑ k ∈ range ((ofNat (n + 1)).segIx - 1), (trailing_zeros k + 1)
          + ∑ k ∈ range 1, (trailing_zeros ((ofNat (n + 1)).segIx - 1 + k) + 1) := by
      exact sum_range_add (fun x ↦ trailing_zeros x + 1) ((ofNat (n + 1)).segIx - 1) 1
    have aux : (ofNat (n + 1)).segIx - 1 + 1 = (ofNat (n + 1)).segIx := by
      refine Nat.sub_add_cancel ?_
      · simp only [ofNat]
        exact segId_ge_one (n + 1)
    simp [aux] at this
    simp [this]
    by_cases at_beg : (ofNat (n + 1)).segIx - 1 = (ofNat n).segIx
    · simp [at_beg]
      sorry
      --
    sorry

/--
Work in progress: Sum of segment heights corresponds to segment index.
-/
theorem t20250904_sorry : ∀ n : ℕ,
    (ofNat (∑ k ∈ Iio (ofNat n).segIx, (trailing_zeros k + 1) - 1)).segIx = (ofNat n).segIx := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have : n = 2 ^ (n.size - 1) ∨ ¬n = 2 ^ (n.size - 1) := eq_or_ne n (2 ^ (n.size - 1))
    rcases this with n_is_pow2|n_ne_pow2
    ·
      sorry
    ·
      sorry

/- #eval List.range 6 |>.map (· + 1) |>.map (2 ^ ·.succ - 2) |>.map
    (fun n ↦
      let state := ofNat n
      let si := state.segIx
      let sh := state.segment_height
      let n' := n - 2 ^ (n.size - 1)
      let as := (ofNat n').segment_height + 1
      f!"(n: {n}, segIx: {si}, height: {sh} ↦ n': {n'}, height': {as})")
-/

/--
Work in progress: Segment index relates to power-of-two subtraction.
-/
theorem segIx_prop_20250914_sorry : ∀ n > 0,
    (ofNat n).segIx = 2 * (ofNat (n - 2 ^ (n.size - 1))).segIx := by
  intro n hn1
  induction n using Nat.strong_induction_on with
  | h n hn =>
    have :
        trailing_zeros (ofNat n).segIx =
        trailing_zeros (ofNat (n - 2 ^ (n.size - 1))).segIx := by
      sorry -- apply?
    sorry
  --

-- これはsegment単位でしか説明できない。これの前にsegIxの関係をいうべき
/--
Work in progress: Segment height preservation property.
-/
theorem segment_height_prop1_sorry : ∀ n > 0, ¬n = 2 ^ (n.size - 1) →
    (ofNat n).segment_height = (ofNat (n - 2 ^ (n.size - 1))).segment_height := by
  intro n hn1 hn2
  simp [segment_height]
  have :
      trailing_zeros (ofNat n).segIx =
      trailing_zeros (ofNat (n - 2 ^ (n.size - 1))).segIx := by
    sorry -- apply?
  sorry
  --

/--
Work in progress: Segment beginning preservation property.
-/
theorem segment_beg_prop1_sorry : ∀ n > 0, n ≠ 2 ^ (n.size - 1) →
    (ofNat n).is_segment_beg = (ofNat (n - 2 ^ (n.size - 1))).is_segment_beg := by
  simp [is_segment_beg, ofNat]
  sorry -- FIXME: todo

/--
Work in progress: Recursive definition of state using toSegIx and toLocIx.
-/
theorem define_recursively2_sorry : ∀ n : ℕ, zero.next n = mk (toSegIx n 0 0) (toLocIx n) := by
  sorry

end WIP

end LubyState
