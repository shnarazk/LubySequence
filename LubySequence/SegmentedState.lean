module

public import LubySequence.SegmentSequence
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

open Segment

/-- save the current state to eliminate recursion -/
public structure SegmentedState where
  /-- segment is -/
  public s : Segment
  /-- the (zero-based) index in segment -/
  public i : ℕ

namespace SegmentedState

@[expose]
public def ofNat (n : ℕ) : SegmentedState :=
  let s := Segment.segmentCovering n
  let i := n - s.start
  ⟨s, i⟩

/-- return the next state -/
@[expose]
public def next (s : SegmentedState) : SegmentedState :=
  if s.i + 1 = s.s.length then ⟨s.s.next, 0⟩ else ⟨s.s, s.i + 1⟩

/-- return the corresponding Luby value -/
@[expose]
public def luby (s : SegmentedState) : ℕ := 2 ^ s.i

/-- `segmentIdOver n ≥ 2` for all n. -/
theorem segmentIdOver_ge_two (n : ℕ) : segmentIdOver n ≥ 2 := by
  simp only [segmentIdOver]
  have h_ex : ∃ i : ℕ, segmentStarts i > n := ⟨n + 2, segmentStarts_gt_self n⟩
  have h0 : ¬(segmentStarts 0 > n) := by simp [segmentStarts]
  have h1 : ¬(segmentStarts 1 > n) := by simp [segmentStarts]
  have hne0 : Nat.find h_ex ≠ 0 := fun heq => h0 (heq ▸ Nat.find_spec h_ex)
  have hne1 : Nat.find h_ex ≠ 1 := fun heq => h1 (heq ▸ Nat.find_spec h_ex)
  omega

/-- `segmentIdCovering n ≥ 1` for all n. -/
theorem segmentIdCovering_ge_one (n : ℕ) : segmentIdCovering n ≥ 1 :=
  Nat.one_le_of_lt (segmentIdCovering_pos n)

/-- `segmentIdCovering n + 1 = segmentIdOver n` -/
theorem segmentIdCovering_add_one (n : ℕ) : segmentIdCovering n + 1 = segmentIdOver n := by
  have := segmentIdOver_ge_two n
  simp only [segmentIdCovering]; omega

/-- `segmentStarts (segmentIdOver n) > n` -/
theorem segmentStarts_over_gt (n : ℕ) : segmentStarts (segmentIdOver n) > n := by
  have h_ex : ∃ i : ℕ, segmentStarts i > n := ⟨n + 2, segmentStarts_gt_self n⟩
  show segmentStarts (Nat.find h_ex) > n
  exact Nat.find_spec h_ex

/-- `segmentStarts (segmentIdCovering n + 1) > n` (the next segment starts after n). -/
theorem segmentStarts_covering_succ_gt (n : ℕ) :
    segmentStarts (segmentIdCovering n + 1) > n := by
  rw [segmentIdCovering_add_one]; exact segmentStarts_over_gt n

/-- For `j < segmentIdOver n`, `segmentStarts j ≤ n`. -/
theorem segmentStarts_lt_over_le (n j : ℕ) (hj : j < segmentIdOver n) :
    segmentStarts j ≤ n := by
  simp only [segmentIdOver] at hj
  have := Nat.find_min _ hj
  omega

/-- `segmentStarts (segmentIdCovering n) ≤ n` -/
theorem segmentStarts_covering_le (n : ℕ) :
    segmentStarts (segmentIdCovering n) ≤ n := by
  apply segmentStarts_lt_over_le
  have := segmentIdOver_ge_two n
  simp only [segmentIdCovering]; omega

/-- `Segment.ofNat t` for `t ≥ 1` has `.start = segmentStarts t`. -/
theorem ofNat_start_eq_segmentStarts (t : ℕ) (ht : t ≥ 1) :
    (Segment.ofNat t).start = segmentStarts t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Segment.ofNat]
  rw [← segmentStarts_to_segment_start]

/-- `Segment.ofNat t` for `t ≥ 1` has `.index = t`. -/
theorem ofNat_index_eq (t : ℕ) (ht : t ≥ 1) :
    (Segment.ofNat t).index = t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Segment.ofNat]
  rw [unfold_segment k]

/-- `Segment.ofNat t` for `t ≥ 1` has `.length = trailingZeros t + 1`. -/
theorem ofNat_length_eq (t : ℕ) (ht : t ≥ 1) :
    (Segment.ofNat t).length = trailingZeros t + 1 := by
  simp only [Segment.length]
  rw [ofNat_index_eq t ht]

/-- The start of segment `t+1` equals start of segment `t` plus length of segment `t`. -/
theorem segmentStarts_succ (t : ℕ) (ht : t ≥ 1) :
    segmentStarts (t + 1) = segmentStarts t + (trailingZeros t + 1) := by
  simp only [segmentStarts]
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [show k + 1 + 1 - 1 = k + 1 from by omega, show k + 1 - 1 = k from by omega]
  rw [Finset.sum_range_succ]

/-- `Segment.next (Segment.ofNat t) = Segment.ofNat (t + 1)` for `t ≥ 1`. -/
theorem segment_next_ofNat (t : ℕ) (ht : t ≥ 1) :
    (Segment.ofNat t).next = Segment.ofNat (t + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Segment.ofNat, Segment.next]
  rfl

/-- `Segment.segmentCovering` unfolds to `Segment.ofNat (segmentIdCovering n)`. -/
theorem segmentCovering_eq (n : ℕ) :
    Segment.segmentCovering n = Segment.ofNat (segmentIdCovering n) := rfl

/-- The start of the covering segment of n. -/
theorem segmentCovering_start (n : ℕ) :
    (Segment.segmentCovering n).start = segmentStarts (segmentIdCovering n) := by
  rw [segmentCovering_eq]
  exact ofNat_start_eq_segmentStarts _ (segmentIdCovering_ge_one n)

/-- The length of the covering segment of n. -/
theorem segmentCovering_length (n : ℕ) :
    (Segment.segmentCovering n).length = trailingZeros (segmentIdCovering n) + 1 := by
  rw [segmentCovering_eq]
  exact ofNat_length_eq _ (segmentIdCovering_ge_one n)

/-- `segmentIdOver` is characterised: it is the least `i` with `segmentStarts i > n`.
    This lemma establishes `segmentIdOver n = m` from witnessing the two Nat.find conditions. -/
theorem segmentIdOver_eq_of_bounds (n m : ℕ)
    (h_gt : segmentStarts m > n)
    (h_min : ∀ j < m, segmentStarts j ≤ n) :
    segmentIdOver n = m := by
  simp only [segmentIdOver]
  have h_ex : ∃ i : ℕ, segmentStarts i > n := ⟨m, h_gt⟩
  refine (Nat.find_eq_iff h_ex).mpr ⟨h_gt, ?_⟩
  intro j hj; exact not_lt.mpr (h_min j hj)

/-- When `n + 1` is still in the same segment, `segmentIdCovering (n + 1) = segmentIdCovering n`. -/
theorem segmentIdCovering_same (n : ℕ)
    (h : n + 1 < segmentStarts (segmentIdCovering n + 1)) :
    segmentIdCovering (n + 1) = segmentIdCovering n := by
  -- Let k = segmentIdCovering n, so segmentIdOver n = k + 1
  -- We know segmentStarts (k+1) > n+1 > n, and for j < k+1, segmentStarts j ≤ n ≤ n+1.
  -- So segmentIdOver (n+1) = k+1 as well, hence segmentIdCovering (n+1) = k.
  have hk := segmentIdCovering_ge_one n
  have h_over_eq : segmentIdOver (n + 1) = segmentIdCovering n + 1 := by
    apply segmentIdOver_eq_of_bounds
    · exact h
    · intro j hj
      have := segmentStarts_lt_over_le n j (by rw [← segmentIdCovering_add_one]; exact hj)
      omega
  -- segmentIdCovering (n+1) = segmentIdOver (n+1) - 1 = (segmentIdCovering n + 1) - 1 = segmentIdCovering n
  show segmentIdOver (n + 1) - 1 = segmentIdCovering n
  omega

/-- When `n + 1` crosses to the next segment, `segmentIdCovering (n + 1) = segmentIdCovering n + 1`. -/
theorem segmentIdCovering_next (n : ℕ)
    (h : n + 1 = segmentStarts (segmentIdCovering n + 1)) :
    segmentIdCovering (n + 1) = segmentIdCovering n + 1 := by
  -- Let k = segmentIdCovering n, so segmentIdOver n = k + 1.
  -- We have n + 1 = segmentStarts (k+1).
  -- segmentStarts (k+2) > segmentStarts (k+1) = n+1, so k+2 witnesses the upper bound.
  -- For j < k+2, i.e. j ≤ k+1: segmentStarts j ≤ segmentStarts (k+1) = n+1.
  have hk := segmentIdCovering_ge_one n
  have h_over_eq : segmentIdOver (n + 1) = segmentIdCovering n + 2 := by
    apply segmentIdOver_eq_of_bounds
    · have h_inc : segmentStarts (segmentIdCovering n + 1) < segmentStarts (segmentIdCovering n + 2) :=
        segmentStarts_is_increasing' (by omega) (by omega)
      omega
    · intro j hj
      have hj_le : j ≤ segmentIdCovering n + 1 := by omega
      have := segmentStarts_is_monotone hj_le
      omega
  -- segmentIdCovering (n+1) = segmentIdOver (n+1) - 1 = (segmentIdCovering n + 2) - 1 = segmentIdCovering n + 1
  show segmentIdOver (n + 1) - 1 = segmentIdCovering n + 1
  omega

/--
Incrementing the natural number index by 1 in the `ofNat` representation
is equivalent to calling `next` on the segmented state.
-/
public theorem segmented_state_prop1 (n : ℕ) : ofNat (n + 1) = (ofNat n).next := by
  -- Abbreviate key quantities
  set k := segmentIdCovering n with hk_def
  have hk_ge1 : k ≥ 1 := segmentIdCovering_ge_one n
  have h_start_le : segmentStarts k ≤ n := segmentStarts_covering_le n
  have h_succ_gt : segmentStarts (k + 1) > n := segmentStarts_covering_succ_gt n
  -- Segment covering n
  have h_cov_start : (Segment.segmentCovering n).start = segmentStarts k := segmentCovering_start n
  have h_cov_length : (Segment.segmentCovering n).length = trailingZeros k + 1 := segmentCovering_length n
  -- segmentStarts (k + 1) = segmentStarts k + (trailingZeros k + 1)
  have h_starts_succ : segmentStarts (k + 1) = segmentStarts k + (trailingZeros k + 1) :=
    segmentStarts_succ k hk_ge1
  -- boundary: segmentStarts (k + 1) = start + length
  have h_boundary : segmentStarts (k + 1) = (Segment.segmentCovering n).start + (Segment.segmentCovering n).length := by
    rw [h_cov_start, h_cov_length]; exact h_starts_succ
  -- start ≤ n
  have h_seg_start_le : (Segment.segmentCovering n).start ≤ n := by rw [h_cov_start]; exact h_start_le
  -- Define idx
  set idx := n - (Segment.segmentCovering n).start with hidx_def
  have h_idx_bound : idx < (Segment.segmentCovering n).length := by omega
  -- Case split: does n + 1 cross the segment boundary?
  by_cases h_at_boundary : idx + 1 = (Segment.segmentCovering n).length
  · -- Case 1: n + 1 crosses to next segment (idx + 1 = length)
    have h_n1_eq : n + 1 = segmentStarts (k + 1) := by omega
    have h_cov_n1 : segmentIdCovering (n + 1) = k + 1 :=
      hk_def ▸ segmentIdCovering_next n (hk_def ▸ h_n1_eq)
    -- segmentCovering (n+1) = ofNat (k + 1)
    have h_seg_n1 : Segment.segmentCovering (n + 1) = Segment.ofNat (k + 1) := by
      simp only [Segment.segmentCovering, h_cov_n1]
    -- seg.next = ofNat (k + 1)
    have h_seg_next : (Segment.segmentCovering n).next = Segment.ofNat (k + 1) := by
      rw [segmentCovering_eq]; exact segment_next_ofNat k hk_ge1
    -- start of next segment
    have h_start_n1 : (Segment.ofNat (k + 1)).start = segmentStarts (k + 1) :=
      ofNat_start_eq_segmentStarts (k + 1) (by omega)
    -- (n + 1) - start of next = 0
    have h_idx_zero : n + 1 - (Segment.ofNat (k + 1)).start = 0 := by
      rw [h_start_n1]; omega
    -- Unfold and show both sides equal ⟨ofNat(k+1), 0⟩
    show (⟨Segment.segmentCovering (n + 1), n + 1 - (Segment.segmentCovering (n + 1)).start⟩ : SegmentedState) =
      next ⟨Segment.segmentCovering n, n - (Segment.segmentCovering n).start⟩
    simp only [next]
    rw [if_pos h_at_boundary]
    rw [h_seg_n1, h_idx_zero, h_seg_next]
  · -- Case 2: n + 1 stays in same segment (idx + 1 < length)
    have h_n1_lt : n + 1 < segmentStarts (k + 1) := by omega
    have h_cov_n1 : segmentIdCovering (n + 1) = k :=
      hk_def ▸ segmentIdCovering_same n (hk_def ▸ h_n1_lt)
    -- segmentCovering (n+1) = segmentCovering n
    have h_seg_n1 : Segment.segmentCovering (n + 1) = Segment.segmentCovering n := by
      simp only [Segment.segmentCovering, h_cov_n1, hk_def]
    -- (n + 1) - start = idx + 1
    have h_idx_succ : n + 1 - (Segment.segmentCovering n).start = idx + 1 := by omega
    -- Unfold and show both sides equal ⟨seg, idx + 1⟩
    show (⟨Segment.segmentCovering (n + 1), n + 1 - (Segment.segmentCovering (n + 1)).start⟩ : SegmentedState) =
      next ⟨Segment.segmentCovering n, n - (Segment.segmentCovering n).start⟩
    simp only [next]
    rw [if_neg h_at_boundary]
    rw [h_seg_n1, h_idx_succ]

end SegmentedState
