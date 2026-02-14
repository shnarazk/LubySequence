module

public import Mathlib.Tactic
public import Mathlib.Data.Nat.Find
-- public import LubySequence.Utils
-- public import LubySequence.Basic
public import LubySequence.TrailingZeros

attribute [local simp] Nat.binaryRec

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
public instance repl : Repr Segment where
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
For `s = 0`, returns a segment with index 1 and start 0.
For `s > 0`, returns the segment reached after `s - 1` steps from `one`.
-/
@[expose, simp]
public def ofNat (t : ℕ) : Segment := match t with
  | 0 => one
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
It is an (zero-based) index, not a (one-based) segment index.
-/
@[expose]
public def segment_starts (t : ℕ) : ℕ := ∑ i ∈ range (t - 1), (trailing_zeros (i + 1) + 1)

-- Examples showing segment_starts computation
-- example : segment_starts 0 = 0 -- 0 is not a valid segment index
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
  have aux : ∑ i ∈ range n, 1 = n := sum_range_induction (fun k ↦ 1) id rfl n fun k ↦ congrFun rfl
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
Find the smallest segment index whose start position exceeds `n`.
Uses `Nat.find` to locate the smallest index where `segment_starts` exceeds `n`,
which identifies the boundary between segments covering and not covering position `n`.
-/
@[expose]
public def segmentIdOver (n : ℕ) : ℕ :=
  Nat.find (by use n + 2 ; exact segment_starts_gt_self n : ∃ i : ℕ, segment_starts i > n)

/--
Find the smallest segment index whose start position is at least `n`.
Uses `Nat.find` to locate the smallest index `i` where `segment_starts i ≥ n`,
identifying the segment that covers position `n`.
This is the non-strict variant of `segmentIdOver`, which uses `>` instead of `≥`.
-/
@[expose]
public def segmentIdCovering (n : ℕ) : ℕ :=
  have s1 : n + 1 > 0 := by exact Nat.zero_lt_succ n
  have s2 : segment_starts (n + 1) ≥ n := by
    have : segment_starts (n - 1 + 2) > n - 1 := by exact segment_starts_gt_self (n - 1)
    replace : segment_starts (n - 1 + 2) ≥ n := by exact Nat.le_of_pred_lt this
    exact segment_starts_ge_self n
  Nat.find (by exact Exists.intro (n + 1) ⟨s1, s2⟩ : ∃ i > 0, segment_starts i ≥ n)

/--
The segment ID covering position 0 is 2.
This is the base case showing that position 0 lies within the first segment,
which has index 1, so `segmentIdOver 0` returns the next segment's index (2).
-/
public theorem segmentIdOver_0 : segmentIdOver 0 = 2 := by
  simp [segmentIdOver]
  refine
    (Nat.find_eq_iff
          (Eq.ndrec (motive := fun {p} ↦ ∀ [DecidablePred p], ∃ n, p n)
            (fun [DecidablePred fun i ↦ segment_starts i > 0] ↦ segmentIdOver._proof_1 0)
            (funext fun i ↦ gt_iff_lt._simp_1))).mpr
      ?_
  · constructor
    · simp [segment_starts]
    · intro n n_def
      replace n_def : n ≤ 1 := Nat.le_of_succ_le_succ n_def
      obtain n_eq_1|n_eq_0 : n = 1 ∨ n < 1 := by exact Nat.eq_or_lt_of_le n_def
      · simp [n_eq_1, segment_starts]
      · replace n_eq_0 : n = 0 := by exact Nat.lt_one_iff.mp n_eq_0
        simp [n_eq_0]
        simp [segment_starts]

/--
The segment ID covering position 0 is 1.
Since `segment_starts i ≥ 0` holds for all `i` and the `i > 0` constraint
excludes 0, `Nat.find` returns the smallest positive `i`, which is 1.
-/
public theorem segmentIdCovering_0 : segmentIdCovering 0 = 1 := by
  simp [segmentIdCovering]
  rw [Nat.find_eq_iff]
  exact ⟨by simp, fun n hn => by omega⟩

/--
Extend the initial segment to cover position `limit`.
Returns the segment that contains position `limit` by advancing from `one`
using `findLargestCoveredSegment` to determine the appropriate number of steps.
-/
@[expose]
public def segmentOver (limit : ℕ) : Segment := Segment.ofNat (segmentIdOver limit)

/--
Returns the segment including index `n`.
-/
@[expose]
public def segmentCovering (n : ℕ) : Segment := Segment.ofNat (segmentIdCovering n)

-- #eval List.range 20 |>.map fun t ↦ (t + 2, segmentIdOver (one + t).start, (one + (t + 1)).index)
/--
For any segment `one + t`, the segment ID covering its start position is the next segment's index.
Specifically, `segmentIdOver (one + t).start = (one + (t + 1)).index`.
This establishes the relationship between segment positions and their covering segment IDs.
-/
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
      replace t'_cond : t' ≤ n + 1 := Nat.le_of_succ_le_succ t'_cond
      replace t'_cond : t' - 1 ≤ n := Nat.sub_le_of_le_add t'_cond
      obtain eq|lt : t' - 1 = n ∨ t' - 1 < n := Nat.eq_or_lt_of_le t'_cond
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

private theorem ofNat_index : ∀ n, (Segment.ofNat n).index = max n 1 := by
  intro n
  cases n with
  | zero => simp [ofNat]
  | succ k => simp only [ofNat]; rw [unfold_segment_index]; omega

public theorem covering_segment_is_self : ∀ t : ℕ,
    (Segment.ofNat (segmentIdCovering (one + t).start)).index = (one + t).index := by
  intro t
  cases t with
  | zero =>
    simp only [HAdd.hAdd, next, segmentIdCovering_0, ofNat, one]
  | succ n =>
    rw [ofNat_index, unfold_segment_index]
    suffices h : segmentIdCovering (one + (n + 1)).start = n + 2 by omega
    simp only [segmentIdCovering]
    rw [Nat.find_eq_iff]
    constructor
    · constructor
      · grind
      · rw [←segment_starts_to_segment_start]
    · -- ∀ i < n + 2, ¬(segment_starts i ≥ (one + (n + 1)).start)
      intro i hi hge
      obtain rfl | hpos := Nat.eq_zero_or_pos i
      · -- i = 0: segment_starts 0 ≤ segment_starts 1 < (one + (n + 1)).start
        have h1 : segment_starts 0 ≤ segment_starts 1 := segment_starts_is_monotone (by omega)
        have h2 : segment_starts 1 < (one + (n + 1)).start := by
          rw [←segment_starts_to_segment_start]
          exact segment_starts_is_increasing' (by omega) (by omega)
        omega
      · -- i > 0 and i < n + 2: strict monotonicity gives contradiction
        have : segment_starts i < (one + (n + 1)).start := by
          rw [←segment_starts_to_segment_start]
          exact segment_starts_is_increasing' hpos hi
        omega

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
      obtain eq|lt : t' - 1 = t + 1 ∨ t' - 1 < t + 1 := by exact Nat.eq_or_lt_of_le t'_cond
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

-- #eval List.range 30 |>.map (fun n ↦ (n + 2, segmentIdOver (∑ i ∈ Finset.range n, (trailing_zeros (i + 1) + 1))))

/--
For any `n`, the segment ID covering the cumulative sum of segment lengths equals `n + 2`.
Specifically, `segmentIdOver (∑ i ∈ range n, (trailing_zeros (i + 1) + 1)) = n + 2`.
This relates the position computed from summing segment lengths to the segment index.
-/
public theorem segmentOver_of_sum_of_trailing_zeros :
    ∀ n : ℕ, segmentIdOver (∑ i ∈ Finset.range n, (trailing_zeros (i + 1) + 1)) = n + 2 := by
  intro n
  induction n with
  | zero => simp [segmentIdOver_0]
  | succ n ih =>
    rw [sum_range_succ]
    simp [segmentIdOver]
    refine
      (Nat.find_eq_iff
            (Eq.ndrec (motive := fun {p} ↦ ∀ [DecidablePred p], ∃ n, p n)
              (fun
                  [DecidablePred fun i ↦
                      segment_starts i >
                        ∑ x ∈ range n, (trailing_zeros (x + 1) + 1) +
                          (trailing_zeros (n + 1) + 1)] ↦
                segmentIdOver._proof_1
                  (∑ x ∈ range n, (trailing_zeros (x + 1) + 1) + (trailing_zeros (n + 1) + 1)))
              (funext fun i ↦ gt_iff_lt._simp_1))).mpr
        ?_
    · constructor
      · have : ∑ x ∈ range n, (trailing_zeros (x + 1) + 1) + (trailing_zeros (n + 1) + 1) =
            ∑ x ∈ range (n + 1), (trailing_zeros (x + 1) + 1) := by
          exact Eq.symm (sum_range_succ (fun x ↦ trailing_zeros (x + 1) + 1) n)
        simp [this]
        rw [←unfold_segment_start]
        rw [←segment_starts_to_segment_start]
        exact segment_starts_is_increasing' (Nat.zero_lt_succ (n + 1)) (Nat.lt_succ_self (n + 1 + 1))
      · intro n' n'_def
        have : ∑ x ∈ range n, (trailing_zeros (x + 1) + 1) + (trailing_zeros (n + 1) + 1) =
            ∑ x ∈ range (n + 1), (trailing_zeros (x + 1) + 1) := by
          exact Eq.symm (sum_range_succ (fun x ↦ trailing_zeros (x + 1) + 1) n)
        simp [this]
        rw [←unfold_segment_start]
        rw [←segment_starts_to_segment_start]
        replace n'_def : n' ≤ n + 1 + 1 := by exact Nat.le_of_succ_le_succ n'_def
        exact segment_starts_is_monotone n'_def

public theorem unfold_segmentIdOver_start (t : ℕ) : segmentIdOver (one + t).start = t + 2 := by
  -- have s1 : segmentIdOver (∑ i ∈ Finset.range t, (trailing_zeros (i + 1) + 1)) = t + 2 := by
  --   exact segmentOver_of_sum_of_trailing_zeros t
  have s2 : (∑ i ∈ Finset.range t, (trailing_zeros (i + 1) + 1)) = (one + t).start := by
    exact Eq.symm (unfold_segment_start t)
  rw [←s2]
  exact segmentOver_of_sum_of_trailing_zeros t

public theorem unfold_segmentIdOver_of_sum (t : ℕ) : segmentIdOver (∑ i ∈ Finset.range t, (trailing_zeros (i + 1) + 1)) = t + 2 := by
  have unfold_segment_start (t : ℕ): (one + t).start = ∑ i ∈ Finset.range t, (trailing_zeros (i + 1) + 1) := by
    exact unfold_segment_start t
  simp only [←unfold_segment_start]
  -- have s2 : (∑ i ∈ Finset.range t, (trailing_zeros (i + 1) + 1)) = (one + t).start := by
  --   exact Eq.symm (unfold_segment_start t)
  -- rw [←s2]
  simp only [next_segment_is_covering_segment]
  simp only [unfold_segment_index]

/-- `segmentIdCovering m` is at most `j` whenever `j > 0` and `segment_starts j ≥ m`. -/
private theorem segmentIdCovering_le {m j : ℕ} (hj_pos : j > 0) (hj_ge : segment_starts j ≥ m) :
    segmentIdCovering m ≤ j := by
  simp only [segmentIdCovering]
  apply Nat.find_min'
  constructor
  · exact hj_pos
  · exact hj_ge

/-- The value returned by `segmentIdCovering` is always positive. -/
private theorem segmentIdCovering_pos (m : ℕ) : segmentIdCovering m > 0 := by
  have h : ∃ i > 0, segment_starts i ≥ m := ⟨m + 1, by omega, segment_starts_ge_self m⟩
  obtain ⟨hpos, _⟩ := Nat.find_spec h
  show Nat.find h > 0
  exact hpos

/-- `segment_starts (segmentIdCovering m) ≥ m`: the covering segment starts at or after `m`. -/
private theorem segmentIdCovering_ge (m : ℕ) : segment_starts (segmentIdCovering m) ≥ m := by
  have h : ∃ i > 0, segment_starts i ≥ m := ⟨m + 1, by omega, segment_starts_ge_self m⟩
  obtain ⟨_, hge⟩ := Nat.find_spec h
  show segment_starts (Nat.find h) ≥ m
  exact hge

/-- The segment of the next index is same or add one. -/
public theorem segmentId_is_continuous (n : ℕ) : segmentIdCovering n = segmentIdCovering (n + 1) ∨ segmentIdCovering n + 1 = segmentIdCovering (n + 1) := by
  -- Lower bound: segmentIdCovering is monotone (weaker predicate ⇒ smaller Nat.find)
  have lb : segmentIdCovering n ≤ segmentIdCovering (n + 1) := by
    simp only [segmentIdCovering]
    apply Nat.find_mono
    intro i hi
    exact ⟨hi.1, by omega⟩
  -- Upper bound: segmentIdCovering n + 1 is a valid candidate for segmentIdCovering (n + 1)
  have ub : segmentIdCovering (n + 1) ≤ segmentIdCovering n + 1 := by
    have hpos := segmentIdCovering_pos n
    have hge := segmentIdCovering_ge n
    have h_incr : segment_starts (segmentIdCovering n) < segment_starts (segmentIdCovering n + 1) :=
      segment_starts_is_increasing' hpos (by omega : segmentIdCovering n < segmentIdCovering n + 1)
    exact segmentIdCovering_le (by omega) (by omega)
  -- Combine: k ≤ segmentIdCovering (n + 1) ≤ k + 1 implies equality to k or k + 1
  rcases Nat.eq_or_lt_of_le lb with h1 | h1
  · left; exact h1
  · right; omega

/--
For a power of two `n = 2 ^ (n.size - 1)`, the segment ID covering position `2 * n - 1`
(the last position of the envelope of size `2 * n`) equals `n + 2`.

This is the conditional form: the hypothesis restricts `n` to be a power of two,
since `n = 2 ^ (n.size - 1)` holds exactly when `n` is a power of two.
The proof rewrites the position `2 * n - 1` as the cumulative sum of trailing-zeros-based
segment lengths via `sum_of_trailing_zeros_prop`, then applies `unfold_segmentIdOver_of_sum`.
-/
public theorem segmentIdOver_at_next_of_envelope1 (n : ℕ) : n = 2 ^ (n.size - 1) → segmentIdOver ((2 : ℕ) * n - 1) = n + 2 := by
  intro hn
  rw (occs := .pos [1]) [←sum_of_trailing_zeros_prop n hn]
  simp only [unfold_segmentIdOver_of_sum]

/--
For any `n`, the segment ID covering position `2 ^ (n + 1) - 1`
(the last position of the envelope of size `2 ^ (n + 1)`) equals `2 ^ n + 2`.

This is the unconditional specialization of `segmentIdOver_at_next_envelope1` obtained by
setting `n := 2 ^ k`. The hypothesis `2 ^ k = 2 ^ ((2 ^ k).size - 1)` is
discharged automatically using `size_of_pow2_eq_self_add_one`, which gives
`(2 ^ k).size = k + 1`.
-/
public theorem segmentIdOver_at_next_of_envelope1' (n : ℕ) : segmentIdOver (2 ^ (n + 1) - 1) = 2 ^ n + 2 := by
  have h : (2 : ℕ) ^ n = 2 ^ ((2 ^ n).size - 1) := by
    rw [size_of_pow2_eq_self_add_one]; simp
  rw [pow_succ, mul_comm]
  exact segmentIdOver_at_next_of_envelope1 (2 ^ n) h

/--
For any `n`, the segment ID covering position `2 ^ (n + 1) - 2`
(the last position before the next envelope boundary) equals `2 ^ n + 1`.

This follows by rewriting the envelope position as the cumulative sum of segment lengths,
then applying the characterization of `segmentIdOver` via `Nat.find` and
monotonicity of `segment_starts`.
-/
public theorem segmentIdOver_at_envelope (n : ℕ) : segmentIdOver (2 ^ (n + 1) - 2) = 2 ^ n + 1 := by
  have hpow : (2 : ℕ) ^ n = 2 ^ ((2 ^ n).size - 1) := by
    rw [size_of_pow2_eq_self_add_one]; simp
  have hsum : ∑ i ∈ range (2 ^ n), (trailing_zeros (i + 1) + 1) = 2 ^ (n + 1) - 1 := by
    simpa [pow_succ, mul_comm] using (sum_of_trailing_zeros_prop (2 ^ n) hpow)
  have hstart : segment_starts (2 ^ n + 1) = 2 ^ (n + 1) - 1 := by
    simp [segment_starts, hsum]
  simp [segmentIdOver]
  refine
    (Nat.find_eq_iff
          (Eq.ndrec (motive := fun {p} ↦ ∀ [DecidablePred p], ∃ n, p n)
            (fun [DecidablePred fun i ↦ segment_starts i > 2 ^ (n + 1) - 2] ↦
              segmentIdOver._proof_1 (2 ^ (n + 1) - 2))
            (funext fun i ↦ gt_iff_lt._simp_1))).mpr ?_
  constructor
  · simp [hstart]
    refine Nat.sub_succ_lt_self (2 ^ (n + 1)) 1 ?_
    · exact Nat.one_lt_two_pow' n
  · intro t ht
    have ht' : t ≤ 2 ^ n := by exact Nat.le_of_succ_le_succ ht
    have hmono : segment_starts t ≤ segment_starts (2 ^ n) := segment_starts_is_monotone ht'
    have hinc : segment_starts (2 ^ n) < segment_starts (2 ^ n + 1) := by
      exact segment_starts_is_increasing' (Nat.two_pow_pos n) (lt_add_one (2 ^ n))
    have hle : segment_starts (2 ^ n) ≤ 2 ^ (n + 1) - 2 := by
      have hlt : segment_starts (2 ^ n) < 2 ^ (n + 1) - 1 := by
        simpa [hstart] using hinc
      exact Nat.le_pred_of_lt hlt
    exact Nat.not_lt_of_ge (Nat.le_trans hmono hle)

/--
For positive `n`, the segment that covers position `2 ^ (n + 1) - 2`
has length `1`.

The proof uses `segmentId_at_envelope` to identify the segment index and
then shows `trailing_zeros (2 ^ n + 1) = 0`, so the length
`trailing_zeros (2 ^ n + 1) + 1` equals `1`.
-/
public theorem segment_length_at_next_of_envelope (n : ℕ) (hn : n > 0) :
    (Segment.ofNat (segmentIdOver (2 ^ (n + 1) - 2))).length = 1 := by
  rw [segmentIdOver_at_envelope]
  have hlt : (1 : ℕ) < 2 ^ n := by
    exact Nat.one_lt_two_pow (Nat.ne_of_gt hn)
  have htz' : trailing_zeros (1 + 2 ^ n) = trailing_zeros 1 := by
    refine trailing_zeros_prop7 n 1 ?_ ?_
    · exact hlt
    · exact Nat.one_ne_zero
  have htz1 : trailing_zeros (1 + 2 ^ n) = 0 := by
    simpa [trailing_zeros1] using htz'
  have htz : trailing_zeros (2 ^ n + 1) = 0 := by
    simpa [add_comm] using htz1
  have h_ofNat : Segment.ofNat (2 ^ n + 1) = one + 2 ^ n := by rfl
  rw [h_ofNat, unfold_segment_length]
  simp [htz]

/--
For `n > 0` with `n = 2 ^ n.size - 2` (i.e., `n` is two less than a power of two),
the start position of `segmentOver n` minus one equals `n`.

This follows from `segmentIdOver_at_envelope`, which identifies the covering segment,
and `sum_of_trailing_zeros_prop`, which computes its start position.
-/
public theorem envelop_segment_prop1 : ∀ n > 0, n = 2 ^ n.size - 2 → (segmentOver n).start - 1 = n := by
  intro n n_gt_0 n_eq
  -- Step 1: n.size ≥ 2 (since n > 0 and n = 2^(n.size) - 2)
  have h_size_ge : n.size ≥ 2 := by
    have : n.size ≥ 1 := Nat.size_pos.mpr n_gt_0
    by_contra h; push_neg at h
    have : n.size = 1 := by omega
    rw [this] at n_eq; norm_num at n_eq; omega
  -- Step 2: Let k = n.size - 1, so n.size = k + 1 and n = 2^(k+1) - 2
  set k := n.size - 1
  have hk : n.size = k + 1 := by omega
  have n_eq' : n = 2 ^ (k + 1) - 2 := by rw [← hk]; exact n_eq
  -- Step 3: segmentIdOver n = 2^k + 1
  have h_id : segmentIdOver n = 2 ^ k + 1 := by
    rw [n_eq']; exact segmentIdOver_at_envelope k
  -- Step 4: Unfold segmentOver to (one + 2^k)
  have h_ofNat : Segment.ofNat (2 ^ k + 1) = one + 2 ^ k := rfl
  simp only [segmentOver, h_id, h_ofNat]
  -- Step 5: Compute start via sum_of_trailing_zeros_prop
  rw [unfold_segment_start]
  have h_pow : (2 : ℕ) ^ k = 2 ^ (((2 : ℕ) ^ k).size - 1) := by
    rw [size_of_pow2_eq_self_add_one]; simp
  rw [sum_of_trailing_zeros_prop _ h_pow, n_eq']
  -- Step 6: Arithmetic: 2 * 2^k - 1 - 1 = 2^(k+1) - 2
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k from by rw [pow_succ, mul_comm]]
  have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  omega

end Segment
