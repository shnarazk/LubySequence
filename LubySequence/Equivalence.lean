module

public import Mathlib.Tactic
public import LubySequence.Basic
public import LubySequence.SegmentSequence
public import LubySequence.TrailingZeros

open Nat

attribute [local simp] binaryRec

open Finset Segment

-- #eval (lubyViaSegment 0, Luby.luby 0)
-- #eval (lubyViaSegment 1, Luby.luby 1)
-- #eval (lubyViaSegment 2, Luby.luby 2)

/- ### Helper lemmas for the main equivalence theorem -/

/--
Shift identity for segmentStarts: adding `2^a` to the segment index shifts
the start position by `2^(a+1) - 1`.
This captures the self-similar structure of the Luby sequence segments.
-/
theorem segmentStarts_shift (a : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ a) :
    segmentStarts (2 ^ a + m) = (2 ^ (a + 1) - 1) + segmentStarts m := by
  simp only [segmentStarts]
  -- Rewrite 2^a + m - 1 = 2^a + (m - 1) since m ≥ 1
  have h_sub : 2 ^ a + m - 1 = 2 ^ a + (m - 1) := by omega
  rw [h_sub, Finset.sum_range_add]
  -- First part: ∑ i ∈ range (2^a), (trailingZeros (i+1)+1) = 2^(a+1) - 1
  have h_pow : (2 : ℕ) ^ a = 2 ^ ((2 ^ a).size - 1) := by
    rw [size_of_pow2_eq_self_add_one]; simp
  have h_first : ∑ i ∈ Finset.range (2 ^ a), (trailingZeros (i + 1) + 1) = 2 ^ (a + 1) - 1 := by
    rw [sum_of_trailingZeros_prop (2 ^ a) h_pow, pow_succ, mul_comm]
  -- Second part: shifted trailingZeros sums equal unshifted ones
  have h_m_lt : m - 1 < 2 ^ a := by omega
  have h_second : ∑ i ∈ Finset.range (m - 1), (trailingZeros (2 ^ a + i + 1) + 1) =
      ∑ i ∈ Finset.range (m - 1), (trailingZeros (i + 1) + 1) := by
    exact trailingZeros_prop9 a (m - 1) h_m_lt
  rw [h_first, h_second]

/- ### Local re-proofs of non-public lemmas needed from other modules -/

/-- Local: `segmentStarts (t + 2) > t`. Delegates to `Segment.segmentStarts_gt_self`. -/
theorem segmentStarts_gt_self' (t : ℕ) : segmentStarts (t + 2) > t :=
  Segment.segmentStarts_gt_self t

/-- Local: `segmentIdCovering m ≥ 1`. Delegates to `Segment.segmentIdCovering_pos`. -/
theorem segmentIdCovering_pos' (m : ℕ) : segmentIdCovering m ≥ 1 :=
  Nat.one_le_of_lt (Segment.segmentIdCovering_pos m)

/-- Local: `S₂ n ≥ 2` for `n > 0`. -/
theorem S₂_ge_two' (n : ℕ) (hn : n > 0) : Luby.S₂ n ≥ 2 := by
  exact Luby.S₂_ge_two n hn

/-- Local: from `isEnvelope n`, derive `S₂ (n + 2) = n + 2`. -/
theorem envelope_S₂_eq (n : ℕ) (h : Luby.isEnvelope n = true) :
    Luby.S₂ (n + 2) = n + 2 := by
  unfold Luby.isEnvelope at h
  exact of_decide_eq_true h

/-- Local: from `isEnvelope n`, derive `n + 2 = 2^j` where `j = (n+3).size - 1`. -/
theorem envelope_gives_pow2 (n : ℕ) (h : Luby.isEnvelope n = true) :
    n + 2 = 2 ^ ((n + 3).size - 1) := by
  have h' := envelope_S₂_eq n h
  simp only [Luby.S₂] at h'
  have : (n + 2).succ = n + 3 := by omega
  rw [this] at h'
  omega

/-- `ofNat(t).start = segmentStarts t` for `t ≥ 1`. -/
theorem ofNat_start_eq (t : ℕ) (ht : t ≥ 1) :
    (Segment.ofNat t).start = segmentStarts t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Segment.ofNat]
  rw [← segmentStarts_to_segment_start]

/-- `ofNat(t)` for `t ≥ 1` equals `one + (t - 1)`. -/
theorem ofNat_succ (t : ℕ) (ht : t ≥ 1) : Segment.ofNat t = (one : Segment) + (t - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rfl

/-- `segmentStarts(2^a + 1) = 2^(a+1) - 1`. -/
theorem segmentStarts_pow2_add_one (a : ℕ) : segmentStarts (2 ^ a + 1) = 2 ^ (a + 1) - 1 := by
  have h := segmentStarts_shift a 1 le_rfl Nat.one_le_two_pow
  have h1 : segmentStarts 1 = 0 := by simp [segmentStarts]
  rw [h1, add_zero] at h
  exact h

/-- Local: `segmentIdCovering n ≤ 2^a` when `n ≤ 2^(a+1) - 2`. -/
theorem segmentIdCovering_le' (a : ℕ) (n : ℕ) (hn : n ≤ 2 ^ (a + 1) - 2) :
    segmentIdCovering n ≤ 2 ^ a := by
  have h_pow_pos : 2 ≤ 2 ^ (a + 1) := by
    have h1 : 2 ^ 1 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h1
  have h_gt : segmentStarts (2 ^ a + 1) > n := by
    rw [segmentStarts_pow2_add_one]; omega
  show segmentIdOver n - 1 ≤ 2 ^ a
  have h_exist : ∃ i, segmentStarts i > n := ⟨n + 2, segmentStarts_gt_self' n⟩
  have h_le : Nat.find h_exist ≤ 2 ^ a + 1 := Nat.find_min' h_exist h_gt
  have h2 := Nat.sub_le_sub_right h_le 1
  rwa [Nat.add_sub_cancel] at h2

/- ### Envelope case -/

/--
At an envelope `n` (where `isEnvelope n`), `lubyViaSegment n = S₂ n`.
-/
theorem lubyViaSegment_at_envelope (n : ℕ) (h : Luby.isEnvelope n = true) :
    lubyViaSegment n = Luby.S₂ n := by
  -- Case split: n = 0 vs n > 0
  obtain rfl | n_pos := Nat.eq_zero_or_pos n
  · -- n = 0: direct computation
    rw [lubyViaSegment_zero_eq_one]
    -- Goal: 1 = Luby.S₂ 0
    -- S₂ 0 = 2 ^ ((0+1).size - 1) = 2 ^ (1.size - 1) = 2 ^ 0 = 1
    have h_size1 : (1 : ℕ).size = 1 := by
      have h1eq : (1 : ℕ) = 2 ^ 0 := by norm_num
      rw [h1eq, size_of_pow2_eq_self_add_one]; norm_num
    show 1 = Luby.S₂ 0
    unfold Luby.S₂
    rw [h_size1]; norm_num
  -- n > 0: extract j from envelope condition
  -- isEnvelope n means S₂ (n + 2) = n + 2, i.e., 2^((n+3).size - 1) = n + 2
  have h_pow := envelope_gives_pow2 n h -- n + 2 = 2 ^ ((n + 3).size - 1)
  set j := (n + 3).size - 1 with hj_def
  -- j ≥ 2 since n ≥ 1 implies n + 2 ≥ 3
  have hj_ge2 : j ≥ 2 := by
    have h4 : (4 : ℕ) ≤ n + 3 := by omega
    have h4s : (4 : ℕ).size ≤ (n + 3).size := Nat.size_le_size h4
    have : (4 : ℕ).size = 3 := by
      show (4 : ℕ).size = 3
      have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4eq, size_of_pow2_eq_self_add_one]
    omega
  have hn_eq : n = 2 ^ j - 2 := by omega
  -- segmentIdOver n = 2^(j-1) + 1  (from segmentIdOver_at_envelope)
  have h_over : segmentIdOver n = 2 ^ (j - 1) + 1 := by
    rw [hn_eq, show j = (j - 1) + 1 from by omega]
    exact segmentIdOver_at_envelope (j - 1)
  -- segmentIdCovering n = 2^(j-1)
  have h_cov : segmentIdCovering n = 2 ^ (j - 1) := by
    simp [segmentIdCovering, h_over]
  -- Unfold lubyViaSegment and S₂, reduce to showing exponents equal
  show 2 ^ (n - (Segment.ofNat (segmentIdCovering n)).start) = 2 ^ (n.succ.size - 1)
  rw [h_cov]
  congr 1
  -- Goal: n - (Segment.ofNat (2 ^ (j - 1))).start = n.succ.size - 1
  -- Step 1: n.succ.size = (n + 1).size = j
  have hn1_size : n.succ.size = j := by
    show (n + 1).size = j
    rw [show n + 1 = 2 ^ j - 1 from by omega]
    exact size_sub (by omega : 0 < j) (by omega : 0 < 1) Nat.one_le_two_pow
  rw [hn1_size]
  -- Goal: n - (Segment.ofNat (2 ^ (j - 1))).start = j - 1
  -- Step 2: Rewrite Segment.ofNat via ofNat_succ
  have hc_pos : 2 ^ (j - 1) ≥ 1 := Nat.one_le_two_pow
  rw [ofNat_succ (2 ^ (j - 1)) hc_pos]
  -- Goal: n - (one + (2 ^ (j - 1) - 1)).start = j - 1
  -- Step 3: Expand start via unfold_segment_start
  rw [unfold_segment_start]
  -- Goal: n - ∑ i ∈ range (2 ^ (j - 1) - 1), (trailingZeros (i + 1) + 1) = j - 1
  -- Step 4: Compute the full sum ∑_{i<2^(j-1)} = 2^j - 1 via sum_of_trailingZeros_prop
  have h_pow_eq : (2 : ℕ) ^ (j - 1) = 2 ^ ((2 ^ (j - 1)).size - 1) := by
    rw [size_of_pow2_eq_self_add_one]; simp
  have h_double : 2 * 2 ^ (j - 1) = 2 ^ j := by
    conv_rhs => rw [show j = (j - 1) + 1 from by omega]
    exact (pow_succ' 2 (j - 1)).symm
  have hsum_full : ∑ i ∈ range (2 ^ (j - 1)), (trailingZeros (i + 1) + 1) = 2 ^ j - 1 := by
    have := sum_of_trailingZeros_prop (2 ^ (j - 1)) h_pow_eq
    rwa [h_double] at this
  -- Step 5: Split off the last term: full_sum = partial_sum + trailingZeros(2^(j-1)) + 1
  have h_split : 2 ^ (j - 1) = (2 ^ (j - 1) - 1) + 1 := by omega
  rw [h_split] at hsum_full
  rw [Finset.sum_range_succ] at hsum_full
  -- Simplify: 2^(j-1) - 1 + 1 = 2^(j-1)
  have h_restore : 2 ^ (j - 1) - 1 + 1 = 2 ^ (j - 1) := by omega
  rw [h_restore] at hsum_full
  -- trailingZeros(2^(j-1)) = j - 1
  have h_tz : trailingZeros (2 ^ (j - 1)) = j - 1 := trailingZeros_prop3 (j - 1)
  rw [h_tz] at hsum_full
  -- hsum_full: partial_sum + (j - 1 + 1) = 2^j - 1, so partial_sum = 2^j - 1 - j
  rw [hn_eq]
  omega

/- ### Non-envelope case -/

/--
For `¬isEnvelope n`, the Luby recursion step preserves the offset within the covering segment.
-/
theorem lubyViaSegment_non_envelope (n : ℕ) (h : ¬(Luby.isEnvelope n = true)) :
    lubyViaSegment n = lubyViaSegment (n + 1 - Luby.S₂ n) := by
  -- n ≥ 1 (since isEnvelope 0 = true)
  have n_pos : n ≥ 1 := by
    by_contra hlt; push Not at hlt
    have : n = 0 := by omega
    subst this
    have : Luby.isEnvelope 0 = true := by simp [Luby.isEnvelope, Luby.S₂, Nat.size, Nat.binaryRec]
    exact h this
  -- Set up notation
  set a := (n + 1).size - 1 with ha_def
  have h_S2 : Luby.S₂ n = 2 ^ a := by simp only [Luby.S₂, ha_def]
  set n' := n + 1 - 2 ^ a with hn'_def
  -- a ≥ 1
  have ha_ge1 : a ≥ 1 := by
    have h1 : (2 : ℕ).size ≤ (n + 1).size := Nat.size_le_size (by omega)
    rw [size2_eq_2] at h1; omega
  -- Size bounds: 2^a ≤ n + 1 < 2^(a+1)
  have h_a1_size : (n + 1).size = a + 1 := by omega
  have h_lower : 2 ^ a ≤ n + 1 := by
    have := @n_ge_subenvelope (n + 1) (by omega)
    simp only [ha_def] at this ⊢; exact this
  have h_upper : n + 1 < 2 ^ (a + 1) := by
    have := Nat.lt_size_self (n + 1)
    rwa [h_a1_size] at this
  -- Not envelope means n + 2 ≠ 2^(a+1)
  have h_not_pow : n + 2 ≠ 2 ^ (a + 1) := by
    intro heq
    have : Luby.isEnvelope n = true := by
      have h_S2_eq : Luby.S₂ (n + 2) = n + 2 := by
        simp only [Luby.S₂]
        have h_succ_eq : (n + 2).succ = 2 ^ (a + 1) + 1 := by omega
        rw [h_succ_eq]
        have h_one_lt : (1 : ℕ) < 2 ^ (a + 1) := by
          calc (1 : ℕ) < 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [size_of_pow2 h_one_lt, size_of_pow2_eq_self_add_one,
            show a + 1 + 1 - 1 = a + 1 from by omega]
        exact heq.symm
      unfold Luby.isEnvelope
      exact decide_eq_true_eq.mpr h_S2_eq
    exact h this
  have h_n_upper : n ≤ 2 ^ (a + 1) - 3 := by omega
  -- n' bounds
  have hn'_le : n' ≤ 2 ^ a - 2 := by simp only [hn'_def]; omega
  have hn'_add : n = n' + (2 ^ a - 1) := by simp only [hn'_def]; omega
  -- Goal: lubyViaSegment n = lubyViaSegment n'
  rw [h_S2]; rw [show n + 1 - 2 ^ a = n' from rfl]
  -- Let t' = segmentIdCovering n'
  set t' := segmentIdCovering n' with ht'_def
  -- t' ≥ 1
  have ht'_ge1 : t' ≥ 1 := segmentIdCovering_pos' n'
  -- t' ≤ 2^(a-1) (since n' ≤ 2^a - 2 = 2^((a-1)+1) - 2)
  have ht'_le : t' ≤ 2 ^ (a - 1) := by
    have h1 : n' ≤ 2 ^ ((a - 1) + 1) - 2 := by
      rw [show (a - 1) + 1 = a from by omega]; exact hn'_le
    exact segmentIdCovering_le' (a - 1) n' h1
  -- Define t = 2^(a-1) + t'
  set t := 2 ^ (a - 1) + t' with ht_def
  -- Key: segmentStarts t = (2^a - 1) + segmentStarts t'
  have h_shift : segmentStarts t = (2 ^ a - 1) + segmentStarts t' := by
    rw [ht_def, show a = (a - 1) + 1 from by omega]
    exact segmentStarts_shift (a - 1) t' ht'_ge1 ht'_le
  -- segmentStarts t' ≤ n' (from the Nat.find characterization)
  have h_over_n' : segmentIdOver n' = t' + 1 := by
    simp only [segmentIdCovering] at ht'_def; omega
  have h_starts_t'_le : segmentStarts t' ≤ n' := by
    have h_lt : t' < segmentIdOver n' := by rw [h_over_n']; omega
    unfold segmentIdOver at h_lt
    have h_neg := Nat.find_min _ h_lt
    omega
  -- segmentStarts t ≤ n
  have h_starts_t_le : segmentStarts t ≤ n := by
    rw [h_shift, hn'_add]; omega
  -- segmentStarts (t + 1) > n
  have h_starts_t1_gt : segmentStarts (t + 1) > n := by
    have ht1_eq : t + 1 = 2 ^ (a - 1) + (t' + 1) := by omega
    rw [ht1_eq]
    -- segmentStarts(segmentIdOver n') > n' by Nat.find_spec
    have h_exist' : ∃ i, segmentStarts i > n' := ⟨n' + 2, segmentStarts_gt_self' n'⟩
    have h_spec : segmentStarts (t' + 1) > n' := by
      rw [← h_over_n']
      exact Nat.find_spec h_exist'
    obtain ht'1_le | ht'1_gt := le_or_gt (t' + 1) (2 ^ (a - 1))
    · -- Use shift identity
      have h_shift1 : segmentStarts (2 ^ (a - 1) + (t' + 1)) =
          (2 ^ a - 1) + segmentStarts (t' + 1) := by
        rw [show a = (a - 1) + 1 from by omega]
        exact segmentStarts_shift (a - 1) (t' + 1) (by omega) ht'1_le
      rw [h_shift1, hn'_add]; omega
    · -- t' = 2^(a-1), so t + 1 = 2^a + 1
      have ht'_eq_bound : t' = 2 ^ (a - 1) := by omega
      have h_rw : 2 ^ (a - 1) + (t' + 1) = 2 ^ a + 1 := by
        rw [ht'_eq_bound]
        have : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ a := by
          rw [← two_pow_succ (a - 1), show a - 1 + 1 = a from by omega]
        omega
      rw [h_rw, segmentStarts_pow2_add_one, hn'_add]; omega
  -- Prove segmentIdCovering n = t
  have h_seg_id : segmentIdCovering n = t := by
    suffices h_over_n : segmentIdOver n = t + 1 by
      simp [segmentIdCovering, h_over_n]
    simp only [segmentIdOver]
    have h_exist : ∃ i, segmentStarts i > n := ⟨n + 2, segmentStarts_gt_self' n⟩
    refine (Nat.find_eq_iff h_exist).mpr ⟨h_starts_t1_gt, ?_⟩
    intro j hj
    exact not_lt.mpr (Nat.le_trans (segmentStarts_is_monotone (by omega : j ≤ t)) h_starts_t_le)
  -- Compute offsets: n - segmentStarts t = n' - segmentStarts t'
  have h_offset_eq : n - segmentStarts t = n' - segmentStarts t' := by
    rw [h_shift, hn'_add]; omega
  -- Conclude: both lubyViaSegment values use the same exponent
  show lubyViaSegment n = lubyViaSegment n'
  rw [lubyViaSegment_def n, lubyViaSegment_def n']
  congr 1
  rw [h_seg_id, ofNat_start_eq t (by omega : t ≥ 1), ofNat_start_eq t' ht'_ge1]
  exact h_offset_eq

/- ### Main theorem -/

/--
The Luby sequence computed via segment structure equals the recursive definition.

The proof is by strong induction on `n`, following the recursion of `Luby.luby`:
- **Envelope case** (`isEnvelope n`): Both sides equal `S₂ n = 2^((n+1).size - 1)`.
  The covering segment has the right length (determined by `trailingZeros`) so the
  power-of-two offset matches `S₂`.
- **Non-envelope case** (`¬isEnvelope n`): The Luby recursion maps `n` to
  `n' = n + 1 - S₂ n`, which lies in the "first half" of the current envelope.
  By `segmentStarts_shift`, the segment structure in the second half mirrors the first,
  preserving the offset. So `lubyViaSegment n = lubyViaSegment n'`, and by the
  inductive hypothesis `lubyViaSegment n' = Luby.luby n'`.
-/
public theorem lubyViaSegment_eq_luby (n : ℕ) : lubyViaSegment n = Luby.luby n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Luby.luby]
    split
    · -- Envelope case
      rename_i h_env
      exact lubyViaSegment_at_envelope n h_env
    · -- Non-envelope case
      rename_i h_nenv
      -- Show n + 1 - S₂ n < n (for the inductive hypothesis)
      have n_pos : n ≥ 1 := by
        by_contra hlt; push Not at hlt
        have : n = 0 := by omega
        subst this
        have : Luby.isEnvelope 0 = true := by simp [Luby.isEnvelope, Luby.S₂, Nat.size, Nat.binaryRec]
        exact h_nenv this
      have h_S2_ge2 : Luby.S₂ n ≥ 2 := S₂_ge_two' n (by omega)
      have h_dec : n + 1 - Luby.S₂ n < n := by omega
      rw [lubyViaSegment_non_envelope n h_nenv]
      exact ih _ h_dec
