module

import Mathlib.Tactic
public import LubySequence.TrailingZeros

/-!
Direct conversion version of segment manipulation
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
@[expose]
public def zero : Segment := ⟨1, 0⟩

instance inst : Inhabited Segment where
  default := zero

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

instance repl : Repr Segment where
  reprPrec s n := "Seg" ++ reprPrec s.index n ++ "@" ++ reprPrec s.start n ++ ":" ++ reprPrec (s.nextStart - 1) n

/--
Compute the next segment(s) after the current one.
The `repeating` parameter specifies how many steps to advance (default is 1).
When `repeating = 0`, returns the current segment unchanged.
For `repeating > 0`, recursively advances through segments.
-/
@[expose, simp]
public def next (self : Segment) (repeating : ℕ := 1) : Segment :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let s := self.next r
    Segment.mk (s.index + 1) s.nextStart

-- #eval List.range 14 |>.map (LubyState.zero.next ·)
-- #eval List.range 14 |>.map (zero.next ·)
-- #eval List.range 10 |>.map (Segment.zero.next ·)

theorem segment_length_gt_0 : ∀ n : ℕ, (Segment.zero.next n).length ≥ 1 := by
  intro n
  induction n with
  | zero => simp [zero, length]
  | succ n ih => rw [next] ; simp [length]

/--
The `next` operation is additive: advancing `a + b` steps is equivalent to
advancing `a` steps and then advancing `b` more steps.
-/
theorem segment_is_additive (a b : ℕ) : zero.next (a + b) = (zero.next a).next b := by
  induction b with
  | zero => simp
  | succ b' ih => simp at ih ; rw [←add_assoc] ; simp [next, ih]

theorem segment_for_n : ∀ n : ℕ,
    Segment.zero.next n = { index := n + 1, start := ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) } := by
  intro n
  induction n with
  | zero => simp [zero]
  | succ n ih =>
    rw [next]
    simp [ih, nextStart, length]
    exact Eq.symm (sum_range_succ (fun x ↦ trailing_zeros (x + 1) + 1) n)

-- #eval List.range 20 |>.map (fun n ↦ (n + 1, (Segment.zero.next n).index))

/--
The index of the segment after `n` steps from the zero segment is `n + 1`.
This establishes a direct relationship between the number of steps and the segment index.
-/
theorem segment_index_for_n : ∀ n : ℕ, (Segment.zero.next n).index = n + 1 := by
  intro n
  simp [segment_for_n]

/--
The length of the segment after `n` steps from zero equals
`trailing_zeros (n + 1) + 1`, which follows from the segment index being `n + 1`.
-/
theorem segment_length_for_n : ∀ n : ℕ, (Segment.zero.next n).length = trailing_zeros (n + 1) + 1 := by
  intro n
  simp [segment_for_n, length]

/- #eval List.range 20
    |>.map (fun n ↦ (n, (Segment.zero.next n).start, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))
-/

/--
The start position of the segment after `n` steps from zero is the sum of
the lengths of all previous segments (each length is `trailing_zeros (i + 1) + 1`).
-/
theorem segment_start_for_n : ∀ n : ℕ, (Segment.zero.next n).start = ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) := by
  intro n
  simp [segment_for_n]

/--
Helper function to find the segment whose start position is within the given limit.
Searches backwards from position `n` to find the last segment that starts before `limit`.

segment は ⟨∑ range x, 1, ∑ range x, (trailing_zeros (i + 1) + 1)⟩ の形で記述できるので
a + xに対する繰り返し回数xを一つ仮定して∑ の形にしてから分割すれば
zero.extendsTo (a + b) = (zero.extendsTo a).extendsTo b
を導出できるのでは?
そのための形は以下のようなもの
-/
public def extendTo (s : Segment) (limit : ℕ) : Segment :=
  if limit = 0 then s else (s.next).extendTo (limit - s.length)
termination_by limit
decreasing_by
  expose_names
  replace h : limit > 0 := by exact Nat.ne_zero_iff_zero_lt.mp h
  have : s.length > 0 := by exact Nat.zero_lt_succ (trailing_zeros s.index)
  exact Nat.sub_lt h this

-- TODO: 補助定理として zero.extendTo (a + b) = (zero.extendTo a).extendTo b が必要

-- TODO: extendTo で置き換え
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
For any positive `n`, the segment within the sum of the first `n` segment lengths
is exactly the (n-1)th segment from zero.
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
For any positive `n`, the sum (start + length) of the segment within the
cumulative sum of segment lengths equals that cumulative sum itself.
This shows that segments partition the sequence correctly.
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

end Segment
