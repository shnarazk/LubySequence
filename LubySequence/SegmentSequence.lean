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
- `within`: Find the segment within a given limit

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
  index : ℕ
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
  | r + 1 =>
    let s := self.next r
    Segment.mk (s.index + 1) s.nextStart

/--
Instance that allows using `+` operator to advance a segment by `n` steps.
This enables the syntax `segment + n` as shorthand for `Segment.next segment n`.
-/
public instance : HAdd Segment Nat Segment where
  hAdd s n := Segment.next s n

/--
The `next` function can be equivalently expressed using the `+` operator.
This theorem establishes that `next s n` and `s + n` are definitionally equal.
-/
public theorem next_as_add : ∀ s : Segment, ∀ n : ℕ, next s n = s + n := by
  intro _ n
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
public theorem segment_start_is_increasing : ∀ n : ℕ, (one + n).start < (one + (n + 1)).start := by
  intro n
  simp only [←next_as_add]
  induction n with
  | zero => simp [nextStart, length]
  | succ n ih =>
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
public def ofNat (s : ℕ) : Segment := match s with
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
public theorem segment_length_gt_0 : ∀ n : ℕ, (one + n).length ≥ 1 := by
  intro n
  simp [length]

/--
Explicit formula for the segment after `n` steps from `one`.
The segment has index `n + 1` and its start position is the sum of all
previous segment lengths, where each length is `trailing_zeros (i + 1) + 1`.
-/
public theorem segment_for_n : ∀ n : ℕ,
    one + n = { index := n + 1, start := ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) } := by
  intro n
  simp only [←next_as_add] at *
  induction n with
  | zero => simp
  | succ n ih =>
    rw [next]
    simp only [ih, nextStart, length]
    have : ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) + (trailing_zeros (n + 1) + 1) =
        ∑ i ∈ range (n + 1), (trailing_zeros (i + 1) + 1) := by
      exact Eq.symm (sum_range_succ (fun x ↦ trailing_zeros (x + 1) + 1) n)
    simp [this]

-- #eval List.range 20 |>.map (fun n ↦ (n + 1, (Segment.zero.next n).index))

/--
The index of the segment after `n` steps from the zero segment is `n + 1`.
This establishes a direct relationship between the number of steps and the segment index.
-/
public theorem segment_index_for_n : ∀ n : ℕ, (one + n).index = n + 1 := by
  intro n
  simp only [segment_for_n n]

/--
The length of the segment after `n` steps from zero equals
`trailing_zeros (n + 1) + 1`, which follows from the segment index being `n + 1`.
-/
public theorem segment_length_for_n : ∀ n : ℕ, (one + n).length = trailing_zeros (n + 1) + 1 := by
  intro n
  simp only [segment_for_n, length]

/- #eval List.range 20
    |>.map (fun n ↦ (n, (Segment.zero.next n).start, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))
-/

/--
The start position of the segment after `n` steps from zero is the sum of
the lengths of all previous segments (each length is `trailing_zeros (i + 1) + 1`).
-/
public theorem segment_start_for_n : ∀ n : ℕ, (one + n).start = ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) := by
  intro n
  simp only [segment_for_n]

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
      refine sum_le_sum_of_subset ?_
      · refine GCongr.finset_range_subset_of_le ?_
        · exact Nat.sub_le m 1
    exact Nat.le_trans ih this

/--
Lower bound for `segment_starts`: for any `s`, `segment_starts (s + 1) ≥ s`.
This follows from the fact that each segment has length at least 1.
-/
theorem segment_starts_ge_self : ∀ s : ℕ, segment_starts (s + 1) ≥ s := by
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
theorem segment_starts_gt_self : ∀ s : ℕ, segment_starts (s + 2) > s := by
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
  rw [segment_for_n n]
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
  Nat.find (by use n + 2 ; exact segment_starts_gt_self n : ∃ t : ℕ, segment_starts t > n)

/--
Extend the initial segment to cover position `limit`.
Returns the segment that contains position `limit` by advancing from `one`
using `findLargestCoveredSegment` to determine the appropriate number of steps.
-/
@[expose]
public def segmentOver (limit : ℕ) : Segment := Segment.ofNat (segmentIdOver limit)

-- #eval List.range 20 |>.map fun n ↦ (n + 2, segmentIdOver (one + n).start, (one + (n + 1)).index)
public theorem segment_is_fixpoint_of_segmentIdOver : ∀ n : ℕ,
    segmentIdOver (one + n).start = (one + (n + 1)).index := by
  intro n
  rw [segment_index_for_n]
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
    · intro n' n'_cond
      replace n'_cond : n' ≤ n + 1 := by exact Nat.le_of_succ_le_succ n'_cond
      replace n'_cond : n' - 1 ≤ n := by exact Nat.sub_le_of_le_add n'_cond
      replace n'_cond : n' - 1 = n ∨ n' - 1 < n := by exact Nat.eq_or_lt_of_le n'_cond
      rcases n'_cond with eq|lt
      · rw [←segment_starts_to_segment_start]
        have : segment_starts n' ≤ segment_starts (n + 1) := by
          refine segment_starts_is_monotone ?_
          · simp [←eq]
            exact le_tsub_add
        exact Nat.le_lt_asymm this
      · rw [←segment_starts_to_segment_start]
        have : segment_starts n' ≤ segment_starts (n + 1) := by
          refine segment_starts_is_monotone ?_
          · replace lt : n' < n + 1 := lt_add_of_tsub_lt_right lt
            exact Nat.le_of_succ_le lt
        exact Nat.le_lt_asymm this

/--
The segment ID for the next start position of a segment equals a specific formula.
This theorem relates segment boundaries to the cumulative segment structure.
-/
theorem extendTo_next_segment : ∀ n : ℕ,
    segmentIdOver (one + n).nextStart = (one + (n + 2)).start := by
  sorry

/-
-- TODO: 補助定理として zero.extendTo (a + b) = (zero.extendTo a).extendTo b が必要

/--
Inductive property for extending segments by addition.
Extending a segment to cover `a + b` positions is equivalent to first extending
to `a` positions, then extending that result to cover `b` more positions.
This is a helper theorem for understanding segment composition.
-/
theorem extendTo_induction (a b : ℕ) : Segment.extendTo (a + b) = (Segment.zero.extendTo a).extendTo b := by
  induction b with
  | zero => rw (occs := .pos [2]) [extendTo] ; simp
  | succ b ih =>
    rw (occs := .pos [1]) [extendTo]
    simp

    sorry

-- TODO: extendTo で置き換え
/--
Helper function for `within` that searches backwards from position `n`.
Recursively finds the largest segment whose start position is at most `limit`,
checking from `n` down to 0.
-/
public def within' (limit : ℕ) (n : ℕ) : Segment := match n with
  | 0 => Segment.zero
  | n' + 1 => if (Segment.zero.next n).start ≤ limit then Segment.zero.next n else within' limit n'

/--
Find the segment whose start position is within the given limit.
This is a wrapper around `within'` that starts the search from `limit` itself.
-/
@[expose, simp]
public def within (limit : ℕ) : Segment := within' limit limit

/- #eval List.range 20 |>.map (fun n ↦ Segment.zero.next n)
#eval List.range 20
    |>.map (fun n ↦ (n, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))
    |>.map (fun (n, m) ↦ (n, m, Segment.zero.next n, within m))
#eval List.range 20
    |>.map (fun n ↦ (n, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))
    |>.map (fun (n, m) ↦ (n, m, within m, within (m + (within m).length), (within m).next))
-/

/--
Inductive property of `within`: extending the limit by the length of the current
segment yields the next segment.
This shows that `within` correctly identifies segment boundaries.
-/
theorem within_induction {n m : ℕ} : within (n + (within n).length) = (within n).next := by
  let s := within n
  have s_def : s = value_of% s := rfl
  simp only [←s_def]
  rw [within, within'.eq_def]
  by_cases n_eq_0 : n = 0
  · simp [n_eq_0] at *
    simp [within'] at s_def
    simp [s_def, zero, length, nextStart]
  · rename' n_eq_0 => n_gt_0
    replace n_gt_0 : n > 0 := by exact Nat.zero_lt_of_ne_zero n_gt_0
    simp
    split <;> expose_names
    · have : s.length ≥ 1 := by exact Nat.le_of_ble_eq_true rfl
      replace : n + s.length > 0 := by exact Nat.add_pos_right n this
      replace : ¬n + s.length = 0 := by exact Nat.ne_zero_iff_zero_lt.mpr this
      exact absurd heq this
    · -- conflict path
      split <;> expose_names
      · have : (zero.next (n + s.length)).start ≥ n + s.length := by sorry
        sorry
      ·
        sorry

/--
For any positive `n`, the segment within the cumulative sum of the first `n` segment lengths
is exactly the segment reached after `n` steps from zero.
This establishes the correctness of the `within` function.
-/
theorem segment_for_within_n :
    ∀ n > 0, within (∑ i ∈ range n, (trailing_zeros (i + 1) + 1)) = Segment.zero.next n := by
  intro n n_gt_0
  induction n with
  | zero => simp  [within']
  | succ n ih =>
    by_cases n_eq_0 : n = 0
    · simp [n_eq_0, within', zero, nextStart, length]
    · rename' n_eq_0 => n_gt_0
      replace n_gt_0 : n > 0 := by exact Nat.zero_lt_of_ne_zero n_gt_0
      replace ih := ih n_gt_0
      sorry

/- def nextTo' (s : Segment) (n : ℕ) : Segment := if s.sum ≥ n then s else (s.next).nextTo' n
termination_by (n - s.sum)
decreasing_by
  expose_names
  simp at h
  simp [next]
  rw (occs := .pos [1]) [sum]
  simp [length]
  refine Nat.sub_lt_sub_left ?_ ?_
  · exact h
  · exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ (trailing_zeros (s.index + 1))) -/

/- #eval List.range 20
    |>.map (fun n ↦ ((within (∑ i ∈ range n, (trailing_zeros (i + 1) + 1))).nextStart,
      ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))
-/

/--
The start position of the segment within the cumulative sum equals that cumulative sum.
This theorem shows that segments partition the Luby sequence correctly:
the start position of each segment aligns exactly with the sum of all previous segment lengths.
-/
theorem segment_sum_eq_segment_length_sum : ∀ n > 0,
    (within (∑ i ∈ range n, (trailing_zeros (i + 1) + 1))).start =
    ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) := by
  intro n n_gt_0
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases n_eq_0 : n = 0
    · rw [n_eq_0]
      simp [range]
      simp [within', nextStart, length, zero]
    · rename' n_eq_0 => n_gt_0
      replace n_gt_0 : n > 0 := by exact Nat.zero_lt_of_ne_zero n_gt_0
      replace ih := ih n_gt_0
      let n' := ∑ i ∈ range 1, (trailing_zeros (n + i + 1) + 1)
      have n'_def : n' = value_of% n' := rfl
      simp at n'_def
      have n'_gt_0 : n' > 0 := by exact Nat.zero_lt_succ (trailing_zeros (n + 0 + 1))
      let sumₙ := ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)
      have sumₙ_def : sumₙ = value_of% sumₙ := rfl
      have : ∑ i ∈ range (n + 1), (trailing_zeros (i + 1) + 1) = sumₙ + n' := by
        exact sum_range_add (fun x ↦ trailing_zeros (x + 1) + 1) n 1
      simp only [this]
      simp only [←sumₙ_def] at * -- ih
      have : (within sumₙ).index = n := by
        sorry
      -- rw [within'.eq_def]
      sorry

/-
theorem t2025114 : ∀ n : ℕ, (state_from (∑ i ∈ range n, (trailing_zeros i + 1))).snd = 0 := by
  intro n
  induction n with
  | zero => simp [state_from, state_from']
  | succ n ih =>
    simp [state_from]
    rw [state_from']
    split <;> expose_names
    · simp at h
      simp
      exact h
    · have : state_from
      sorry
-/
-/

end Segment
