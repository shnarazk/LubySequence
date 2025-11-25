module

import Mathlib.Tactic
public import Mathlib.Data.Nat.Find
public import LubySequence.TrailingZeros

/-!
# Segment Sequence

Direct conversion version of segment manipulation for the Luby sequence.

This module defines `Segment`, a structure that represents contiguous portions of the Luby sequence.
Each segment has an index (starting from 1) and a start position within the sequence.
The module provides functions to navigate between segments, compute segment boundaries,
and establish relationships between segment indices and positions.

## Main Definitions

- `Segment`: A structure with an index and start position
- `one`: The initial segment with index 1 and start position 0
- `next`: Advance a segment by n steps
- `segment_starts`: Compute the cumulative start positions
- `segmentIdOver`, `segmentOver`: Find the segment containing a given position

## Key Theorems

- Segment properties establish monotonicity and correctness of segment boundaries
- Equivalences between different representations of segment positions
-/

open Finset

/--
A segment represents a contiguous portion of the Luby sequence.
Each segment has an index (starting from 1) and a start position.
The segment structure ensures that the index is always at least 1.
-/
public structure Segment where
  /-- (one-based) segment is -/
  index : ℕ
  /-- the (zero-based) index of the element at which this segment starts -/
  start : ℕ

namespace Segment

/--
The initial segment with index 1 and start position 0.
This represents the first segment in the Luby sequence.
-/
@[expose, simp]
public def one : Segment := ⟨1, 0⟩

/--
Default instance for `Segment`, using `one` as the default value.
This allows `Segment` to be used in contexts requiring an `Inhabited` instance.
-/
instance inst : Inhabited Segment where
  default := one

/--
The length of a segment, computed as the number of trailing zeros in its index plus 1.
This corresponds to how many elements in the Luby sequence belong to this segment.
-/
@[expose]
public def length (s : Segment) : ℕ := trailing_zeros s.index + 1

/--
The sum of a segment's start position and its length.
This gives the position where the next segment would start.
-/
@[expose]
public def nextStart (s : Segment) : ℕ := s.start + s.length

/--
Custom string representation for `Segment`.
Displays a segment in the form "Seg{index}@{start}:{end}" where end is `nextStart - 1`.
-/
instance repl : Repr Segment where
  reprPrec s n := "Seg" ++ reprPrec s.index n ++ "@" ++ reprPrec s.start n ++ ":" ++ reprPrec (s.nextStart - 1) n

/--
Compute the `repeating`-th segment after the current one.
The `repeating` parameter specifies how many steps to advance (default is 1).
When `repeating = 0`, returns the current segment unchanged.
For `repeating > 0`, recursively advances through segments.
-/
@[expose, simp]
public def next (self : Segment := one) (repeating : ℕ := 1) : Segment :=
  match repeating with
  | 0     => self
  | t + 1 => let s := self.next t ; Segment.mk (s.index + 1) s.nextStart

/--
Instance that allows using `+` operator to advance a segment by `n` steps.
This enables the syntax `segment + n` as shorthand for `Segment.next segment n`.
-/
public instance : HAdd Segment Nat Segment where
  hAdd s t := Segment.next s t

/--
The `next` function can be equivalently expressed using the `+` operator.
This theorem establishes that `next s n` and `s + n` are definitionally equal.
-/
public theorem next_as_add : ∀ s : Segment, ∀ t : ℕ, next s t = s + t := by
  intro s t
  exact rfl

/--
The `next` operation is additive: advancing `a + b` steps is equivalent to
advancing `a` steps and then advancing `b` more steps.
-/
public theorem segment_add_is_associative (a b : ℕ) : one + (a + b) = (one + a) + b := by
  simp [←next_as_add]
  induction b with
  | zero => exact rfl
  | succ b' ih =>
    simp [next]
    constructor
    · exact congrArg index ih
    · exact congrArg nextStart ih

/--
The start position increases strictly monotonically with each segment step.
For any `n`, the start position of segment `one + (n + 1)` is strictly greater
than the start position of segment `one + n`.
-/
public theorem segment_start_is_increasing : ∀ t : ℕ, (one + t).start < (one + (t + 1)).start := by
  intro t
  simp only [←next_as_add]
  induction t with
  | zero => simp [nextStart, length]
  | succ t ih =>
    simp only [next] at *
    rw (occs := .pos [2]) [nextStart]
    rw [length]
    simp

/--
Convert a natural number to a segment by advancing from the initial segment.
For `s = 0`, returns a segment with index 0 and start 0.
For `s > 0`, returns the segment reached after `s - 1` steps from `one`.
-/
@[expose, simp]
public def ofNat (t : ℕ) : Segment := match t with
  | 0 => ⟨0, 0⟩
  | i + 1 => one + i

-- Basic examples demonstrating segment operations
example : Segment.one.next 0 = { index := 1, start := 0 } := by simp
example : Segment.next one 0 = { index := 1, start := 0 } := by simp
example : Segment.one.next 1 = { index := 2, start := 1 } := by simp [nextStart, length]
example : one + 1 = { index := 2, start := 1 } := by simp [←next_as_add, nextStart, length]
example : Segment.ofNat 1 = { index := 1, start := 0 } := by simp [←next_as_add]
example : Segment.ofNat 2 = { index := 2, start := 1 } := by simp [←next_as_add, nextStart, length]

/--
Every segment reached from `one` has a length of at least 1.
This ensures that segments are non-empty and partition the sequence properly.
-/
public theorem segment_length_gt_0 : ∀ t : ℕ, (one + t).length ≥ 1 := by
  intro t
  simp [length]

/--
Explicit formula for the segment after `n` steps from `one`.
The segment has index `n + 1` and its start position is the sum of all
previous segment lengths, where each length is `trailing_zeros (i + 1) + 1`.
-/
public theorem unfold_segment : ∀ t : ℕ,
    one + t = { index := t + 1, start := ∑ i ∈ range t, (trailing_zeros (i + 1) + 1) } := by
  intro t
  simp only [←next_as_add] at *
  induction t with
  | zero => simp
  | succ t ih =>
    rw [next]
    simp only [ih, nextStart, length]
    have : ∑ i ∈ range t, (trailing_zeros (i + 1) + 1) + (trailing_zeros (t + 1) + 1) =
        ∑ i ∈ range (t + 1), (trailing_zeros (i + 1) + 1) := by
      exact Eq.symm (sum_range_succ (fun x ↦ trailing_zeros (x + 1) + 1) t)
    simp [this]

-- #eval List.range 20 |>.map (fun t ↦ (t + 1, (Segment.zero.next t).index))

/--
The index of the segment after `n` steps from the zero segment is `n + 1`.
This establishes a direct relationship between the number of steps and the segment index.
-/
public theorem unfold_segment_index : ∀ t : ℕ, (one + t).index = t + 1 := by
  intro t
  simp only [unfold_segment t]

/--
The length of the segment after `n` steps from zero equals
`trailing_zeros (n + 1) + 1`, which follows from the segment index being `n + 1`.
-/
public theorem unfold_segment_length : ∀ t : ℕ, (one + t).length = trailing_zeros (t + 1) + 1 := by
  intro t
  simp only [unfold_segment, length]

/- #eval List.range 20
    |>.map (fun n ↦ (n, (Segment.zero.next n).start, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))
-/

/--
The start position of the segment after `n` steps from zero is the sum of
the lengths of all previous segments (each length is `trailing_zeros (i + 1) + 1`).
-/
public theorem unfold_segment_start : ∀ t : ℕ, (one + t).start = ∑ i ∈ range t, (trailing_zeros (i + 1) + 1) := by
  intro t
  simp only [unfold_segment]

/--
Compute the start position for segment index `t`.
Returns the cumulative sum of lengths of the 1 to `t`-th segments.
-/
@[expose]
public def segment_starts (t : ℕ) : ℕ := ∑ i ∈ range (t - 1), (trailing_zeros (i + 1) + 1)

-- Examples showing segment_starts computation
example : segment_starts 0 = 0 := by simp [segment_starts]
example : segment_starts 1 = 0 := by simp [segment_starts]
example : segment_starts 2 = 1 := by simp [segment_starts]
example : segment_starts 3 = 3 := by simp [segment_starts, range, trailing_zeros]

/--
The `segment_starts` function is monotonic: if `a ≤ b`, then `segment_starts a ≤ segment_starts b`.
This follows from the fact that each term in the sum is non-negative.
-/
public theorem segment_starts_is_monotone : ∀ {a b : ℕ}, a ≤ b → segment_starts a ≤ segment_starts b := by
  intros a b h
  induction h with
  | refl => simp [segment_starts]
  | step h ih =>
    expose_names
    have : segment_starts m ≤ segment_starts m.succ := by
      simp [segment_starts]
      exact sum_le_sum_of_subset (GCongr.finset_range_subset_of_le (Nat.sub_le m 1))
    exact Nat.le_trans ih this

/--
Lower bound for `segment_starts`: for any `s`, `segment_starts (s + 1) ≥ s`.
This follows from the fact that each segment has length at least 1.
-/
theorem segment_starts_ge_self : ∀ t : ℕ, segment_starts (t + 1) ≥ t := by
  intro n
  simp [segment_starts]
  have : ∑ i ∈ range n, 1 ≤ ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) := by
    refine sum_le_sum ?_
    · intro i ih
      exact Nat.le_add_left 1 (trailing_zeros (i + 1))
  have aux :∑ i ∈ range n, 1 = n := sum_range_induction (fun k ↦ 1) id rfl n fun k ↦ congrFun rfl
  exact le_of_eq_of_le (id (Eq.symm aux)) this

/--
Strict lower bound for `segment_starts`: for any `s`, `segment_starts (s + 2) > s`.
This is a stronger version of `segment_starts_ge_self`.
-/
theorem segment_starts_gt_self : ∀ t : ℕ, segment_starts (t + 2) > t := by
  intro n
  simp [segment_starts]
  have : ∑ i ∈ range (n + 1), 1 ≤ ∑ i ∈ range (n + 1), (trailing_zeros (i + 1) + 1) := by
    refine sum_le_sum ?_
    · intro i ih
      exact Nat.le_add_left 1 (trailing_zeros (i + 1))
  have aux (n : ℕ) : ∑ i ∈ range n, 1 = n := sum_range_induction (fun k ↦ 1) id rfl n fun k ↦ congrFun rfl
  exact le_of_eq_of_le (id (Eq.symm (aux (n + 1)))) this

/--
Relationship between `segment_starts` and the `start` field of a segment.
For any `n`, `segment_starts (n + 1)` equals the start position of the segment
reached after `n` steps from `one`.
-/
public theorem segment_starts_to_segment_start : ∀ n, segment_starts (n + 1) = (one + n).start := by
  intro n
  simp only [segment_starts]
  rw [unfold_segment n]
  exact rfl

/--
The `segment_starts` function is strictly increasing for positive indices.
If `0 < a < b`, then `segment_starts a < segment_starts b`.
This follows from the fact that each segment has positive length.
-/
public theorem segment_starts_is_increasing' : ∀ {a b : ℕ}, a > 0 → a < b → segment_starts a < segment_starts b := by
  intros a b a_ge_1 h
  simp [segment_starts]
  let d := b - a
  have d_def : d = value_of% d := rfl
  have d_ge_1 : d ≥ 1 := by exact Nat.le_sub_of_add_le' h
  have b_def : b = a + d := by grind
  simp [b_def]
  have : a + d - 1 = a - 1 + d := Nat.sub_add_comm a_ge_1
  simp [this]
  simp [sum_range_add]
  replace : ∑ x ∈ range d, 1 ≤ ∑ x ∈ range d, (trailing_zeros (a - 1 + x + 1) + 1) := by
    refine sum_le_sum ?_
    · intro i i_def
      exact Nat.le_add_left 1 (trailing_zeros (a - 1 + i + 1))
  have aux : ∑ x ∈ range d, 1 = 1 * d := sum_range_induction (fun k ↦ 1) (HMul.hMul 1) rfl d fun k ↦ congrFun rfl 
  simp [aux] at this
  replace aux : 0 < d := d_ge_1
  exact Nat.lt_of_lt_of_le d_ge_1 this

/--
The `segment_starts` function is strictly increasing for positive indices.
For any `a < b`, the start position `(one + a).start` is strictly less than `(one + b).start`.
This is a more convenient form of `segment_starts_is_increasing'` working directly with segments.
-/
public theorem segment_starts_is_increasing : ∀ {a b : ℕ}, a < b → (one + a).start < (one + b).start := by
  intro a b ordering
  simp only [←segment_starts_to_segment_start]
  exact segment_starts_is_increasing' (Nat.zero_lt_succ a) (Nat.add_lt_add_right ordering 1)

/--
Find the largest segment index whose start position does not exceed `n`.
Uses `Nat.find` to locate the smallest index where `segment_starts` exceeds `n`,
which identifies the boundary between segments covering and not covering position `n`.
-/
@[expose]
public def segmentIdOver (n : ℕ) : ℕ := 
  Nat.find (by use n + 2 ; exact segment_starts_gt_self n : ∃ i : ℕ, segment_starts i > n)

/--
Extend the initial segment to cover position `limit`.
Returns the segment that contains position `limit` by advancing from `one`
using `findLargestCoveredSegment` to determine the appropriate number of steps.
-/
@[expose]
public def segmentOver (limit : ℕ) : Segment := Segment.ofNat (segmentIdOver limit)

/--
For any segment `one + t`, the segment ID covering its start position is the next segment's index.
Specifically, `segmentIdOver (one + t).start = (one + (t + 1)).index`.
This establishes the relationship between segment positions and their covering segment IDs.
-/
-- #eval List.range 20 |>.map fun t ↦ (t + 2, segmentIdOver (one + t).start, (one + (t + 1)).index)
public theorem next_segment_is_covering_segment : ∀ t : ℕ,
    segmentIdOver (one + t).start = (one + (t + 1)).index := by
  intro n
  rw [unfold_segment_index]
  simp only [segmentIdOver]
  refine
    (Nat.find_eq_iff
          (Eq.ndrec (motive := fun {p} ↦ ∀ [DecidablePred p], ∃ n, p n)
            (fun [DecidablePred fun t ↦ segment_starts t > (one + n).start] ↦
              segmentIdOver._proof_1 (one + n).start)
            (funext fun t ↦ gt_iff_lt._simp_1))).mpr
      ?_
  · constructor
    · simp only [←segment_starts_to_segment_start]
      exact segment_starts_is_increasing' (Nat.zero_lt_succ n) (lt_add_one (n + 1))
    · intro t' t'_cond
      replace t'_cond : t' ≤ n + 1 := by exact Nat.le_of_succ_le_succ t'_cond
      replace t'_cond : t' - 1 ≤ n := by exact Nat.sub_le_of_le_add t'_cond
      replace t'_cond : t' - 1 = n ∨ t' - 1 < n := by exact Nat.eq_or_lt_of_le t'_cond
      rcases t'_cond with eq|lt
      · rw [←segment_starts_to_segment_start]
        have : segment_starts t' ≤ segment_starts (n + 1) := by
          refine segment_starts_is_monotone ?_
          · simp [←eq]
            exact le_tsub_add
        exact Nat.le_lt_asymm this
      · rw [←segment_starts_to_segment_start]
        have : segment_starts t' ≤ segment_starts (n + 1) := by
          refine segment_starts_is_monotone ?_
          · replace lt : t' < n + 1 := lt_add_of_tsub_lt_right lt
            exact Nat.le_of_succ_le lt
        exact Nat.le_lt_asymm this

/--
For any segment `one + t`, the segment ID covering its `nextStart` position equals `t + 3`.
This is expressed as `segmentIdOver (one + t).nextStart = (one + (t + 2)).index`.
Since `(one + k).index = k + 1` by `unfold_segment_index`, we have
`(one + (t + 2)).index = (t + 2) + 1 = t + 3`.
This characterizes which segment covers the position immediately after a segment ends.
-/
-- #eval List.range 20 |>.map fun t ↦ (t + 2, segmentIdOver (one + t).nextStart, (one + (t + 2)).index)
theorem coveringSegment_of_next_segment_is_next_of_next :
    ∀ t : ℕ, segmentIdOver (one + t).nextStart = (one + (t + 2)).index := by
  intro t
  simp only [unfold_segment_index]
  simp only [nextStart]
  have : (one + t).start + (one + t).length = (one + (t + 1)).start := rfl
  simp only [this]
  simp only [segmentIdOver]
  refine (Nat.find_eq_iff (segmentIdOver._proof_1 (one + (t + 1)).start)).mpr ?_
  · constructor
    · simp only [←segment_starts_to_segment_start]
      exact segment_starts_is_increasing' (Nat.zero_lt_succ (t + 1)) (lt_add_one (t + 2))
    · intro t' t'_cond
      replace t'_cond : t' ≤ t + 2 := by exact Nat.le_of_succ_le_succ t'_cond
      replace t'_cond : t' - 1 ≤ t + 1 := by exact Nat.sub_le_of_le_add t'_cond
      replace t'_cond : t' - 1 = t + 1 ∨ t' - 1 < t + 1 := by exact Nat.eq_or_lt_of_le t'_cond
      rcases t'_cond with eq|lt
      · rw [←segment_starts_to_segment_start]
        have : segment_starts t' ≤ segment_starts (t + 2) := by
          refine segment_starts_is_monotone ?_
          · replace eq : t' = t + 2 := by grind
            exact Nat.le_of_eq eq
        exact Nat.le_lt_asymm this
      · rw [←segment_starts_to_segment_start]
        have : segment_starts t' ≤ segment_starts (t + 2) := by
          refine segment_starts_is_monotone ?_
          · replace lt : t' < t + 2 := by exact lt_of_tsub_lt_tsub_right lt
            exact Nat.le_of_succ_le lt
        exact Nat.le_lt_asymm this

end Segment
