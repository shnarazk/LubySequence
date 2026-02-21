module

public import Mathlib.Tactic
public import LubySequence.Utils
public import LubySequence.Basic
-- public import LubySequence.Segment
public import LubySequence.SegmentSequence
-- public import LubySequence.State
public import LubySequence.TrailingZeros

namespace LubyState

open Nat

attribute [local simp] binaryRec

/-
#eval List.range 10
    |>.map (fun n ↦ 2 ^ (n + 1) - 2)
    |>.map (fun n ↦ (n, (Segment.segmentOver n).start - 1))
-/


-- これはenvelopeはいくつのsegmentを必要とするかという問題。
-- ∑ i ∈ range (2 ^ (k.size - 1)), trailing_zeros · = k から
-- n = 2 ^ n.size - 1 の大きさのenvelopには2 ^ (n.size - 1) segmentsが必要であるため、
-- 次のn + 1に対しては当然2 ^ n.size segmentsが必要。
-- この日本語のコメントは正しいのか？
-- segment_heightはaccumulativeではないので再帰で解ける気がしないのだが。
/-
theorem t20250913_sorry : ∀ n > 0, n = 2 ^ (n.size - 1) - 1 → (ofNat (n - 1)).segment_height = n.size := by
  intro n hn
  let k := n - 1
  have hk : k = value_of% k := by exact rfl
  have hk' : n = k + 1 := by exact (Nat.sub_eq_iff_eq_add hn).mp hk
  simp [hk'] at *
  clear hn hk hk'
  induction k using Nat.strong_induction_on with
  | h k ih =>
    expose_names
    intro h2
    obtain kz|kp : k = 0 ∨ k > 0 := by exact Nat.eq_zero_or_pos k
    · simp [kz, ofNat, default, segment_height]
    · have h2' : k = 2 ^ ((k + 1).size - 1) - 1 - 1 := by exact Nat.eq_sub_of_add_eq h2
      let j := 2 ^ ((k + 1).size - 1 - 1)
      have hj : j = value_of% j := rfl
      have k3 : k ≥ 3 := by
        have k_ge_2 : k ≥ 2 := by
          by_contra k_lt_2
          have k_eq_1 : k = 1 := by
            have : k < 2 := by exact gt_of_not_le k_lt_2
            replace : k = 1 := by exact Nat.eq_of_le_of_lt_succ kp this
            exact this
          rewrite (occs := .pos [2]) [k_eq_1] at h2'
          simp [size] at h2'
          have : ¬k > 0 := by exact Eq.not_gt h2'
          exact absurd kp this
        by_contra k_lt_3
        simp at k_lt_3
        have k_eq_2 : k = 2 := by exact Nat.eq_of_le_of_lt_succ k_ge_2 k_lt_3
        rewrite (occs := .pos [2]) [k_eq_2] at h2'
        simp [size] at h2'
        have : ¬k > 0 := by exact Eq.not_gt h2'
        exact absurd kp this
      have j_ge_2 : j ≥ 2 := by
        have : 3 + 1 ≤ k + 1 := by exact Nat.add_le_add_right k3 1
        replace : (3 + 1).size ≤ (k + 1).size := by exact size_le_size this
        simp at this
        replace : 3 - 1 ≤ (k + 1).size - 1 := by exact Nat.sub_le_sub_right this 1
        replace : 3 - 1 - 1 ≤ (k + 1).size - 1 - 1 := by exact Nat.sub_le_sub_right this 1
        simp at this
        replace : 2 ^ 1 ≤ 2 ^ ((k + 1).size - 1 - 1) := Luby.pow2_le_pow2 1 ((k + 1).size - 1 - 1) this
        simp at this
        exact this
      have j2 : 2 ^ ((k + 1).size - 1) = j + j := by
        simp [hj, ←mul_two]
        refine Eq.symm (two_pow_pred_mul_two ?_)
        · have t1 : 2 ≤ k + 1 := by exact le_add_of_sub_le kp
          replace t1 : (2 : ℕ).size ≤ (k + 1).size := size_le_size t1
          simp at t1
          refine zero_lt_sub_of_lt t1
      simp [j2] at h2'
      have h3 : k = 2 * (j - 1) := by omega
      simp [h3]
      rw [Eq.symm (size_of_even_add_one_eq_size_of_self (j - 1) (zero_lt_sub_of_lt j_ge_2))]
      rw [size_of_double_eq_self_add_one (j - 1) (zero_lt_sub_of_lt j_ge_2)]
      rw [segment_height]
      sorry
-/

open Finset Segment

-- #eval (luby_via_segment 0, Luby.luby 0)
-- #eval (luby_via_segment 1, Luby.luby 1)
-- #eval (luby_via_segment 2, Luby.luby 2)

/-! ### Helper lemmas for the main equivalence theorem -/

/--
Shift identity for segment_starts: adding `2^a` to the segment index shifts
the start position by `2^(a+1) - 1`.
This captures the self-similar structure of the Luby sequence segments.
-/
private theorem segment_starts_shift (a : ℕ) (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 ^ a) :
    segment_starts (2 ^ a + m) = (2 ^ (a + 1) - 1) + segment_starts m := by
  simp only [segment_starts]
  -- Rewrite 2^a + m - 1 = 2^a + (m - 1) since m ≥ 1
  have h_sub : 2 ^ a + m - 1 = 2 ^ a + (m - 1) := by omega
  rw [h_sub, Finset.sum_range_add]
  -- First part: ∑ i ∈ range (2^a), (trailing_zeros (i+1)+1) = 2^(a+1) - 1
  have h_pow : (2 : ℕ) ^ a = 2 ^ ((2 ^ a).size - 1) := by
    rw [size_of_pow2_eq_self_add_one]; simp
  have h_first : ∑ i ∈ Finset.range (2 ^ a), (trailing_zeros (i + 1) + 1) = 2 ^ (a + 1) - 1 := by
    rw [sum_of_trailing_zeros_prop (2 ^ a) h_pow, pow_succ, mul_comm]
  -- Second part: shifted trailing_zeros sums equal unshifted ones
  have h_m_lt : m - 1 < 2 ^ a := by omega
  have h_second : ∑ i ∈ Finset.range (m - 1), (trailing_zeros (2 ^ a + i + 1) + 1) =
      ∑ i ∈ Finset.range (m - 1), (trailing_zeros (i + 1) + 1) := by
    exact trailing_zeros_prop9 a (m - 1) h_m_lt
  rw [h_first, h_second]

/-! ### Local re-proofs of non-public lemmas needed from other modules -/

/-- Local: `segment_starts (t + 2) > t`. Delegates to `Segment.segment_starts_gt_self`. -/
private theorem segment_starts_gt_self' (t : ℕ) : segment_starts (t + 2) > t :=
  Segment.segment_starts_gt_self t

/-- Local: `segmentIdCovering m ≥ 1`. Delegates to `Segment.segmentIdCovering_pos`. -/
private theorem segmentIdCovering_pos' (m : ℕ) : segmentIdCovering m ≥ 1 :=
  Nat.one_le_of_lt (Segment.segmentIdCovering_pos m)

/-- Local: `S₂ n ≥ 2` for `n > 0`. -/
private theorem S₂_ge_two' (n : ℕ) (hn : n > 0) : Luby.S₂ n ≥ 2 := by
  exact Luby.S₂_ge_two n hn

/-- Local: from `is_envelope n`, derive `S₂ (n + 2) = n + 2`. -/
private theorem envelope_S₂_eq (n : ℕ) (h : Luby.is_envelope n = true) :
    Luby.S₂ (n + 2) = n + 2 := by
  unfold Luby.is_envelope at h
  exact of_decide_eq_true h

/-- Local: from `is_envelope n`, derive `n + 2 = 2^j` where `j = (n+3).size - 1`. -/
private theorem envelope_gives_pow2 (n : ℕ) (h : Luby.is_envelope n = true) :
    n + 2 = 2 ^ ((n + 3).size - 1) := by
  have h' := envelope_S₂_eq n h
  simp only [Luby.S₂] at h'
  have : (n + 2).succ = n + 3 := by omega
  rw [this] at h'
  omega

/-- `ofNat(t).start = segment_starts t` for `t ≥ 1`. -/
private theorem ofNat_start_eq (t : ℕ) (ht : t ≥ 1) :
    (Segment.ofNat t).start = segment_starts t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  simp only [Segment.ofNat]
  rw [← segment_starts_to_segment_start]

/-- `ofNat(t)` for `t ≥ 1` equals `one + (t - 1)`. -/
private theorem ofNat_succ (t : ℕ) (ht : t ≥ 1) : Segment.ofNat t = one + (t - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rfl

/-- `segment_starts(2^a + 1) = 2^(a+1) - 1`. -/
private theorem segment_starts_pow2_add_one (a : ℕ) : segment_starts (2 ^ a + 1) = 2 ^ (a + 1) - 1 := by
  have h := segment_starts_shift a 1 le_rfl Nat.one_le_two_pow
  have h1 : segment_starts 1 = 0 := by simp [segment_starts]
  rw [h1, add_zero] at h
  exact h

/-- Local: `segmentIdCovering n ≤ 2^a` when `n ≤ 2^(a+1) - 2`. -/
private theorem segmentIdCovering_le' (a : ℕ) (n : ℕ) (hn : n ≤ 2 ^ (a + 1) - 2) :
    segmentIdCovering n ≤ 2 ^ a := by
  have h_pow_pos : 2 ≤ 2 ^ (a + 1) := by
    have h1 : 2 ^ 1 ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using h1
  have h_gt : segment_starts (2 ^ a + 1) > n := by
    rw [segment_starts_pow2_add_one]; omega
  show segmentIdOver n - 1 ≤ 2 ^ a
  have h_exist : ∃ i, segment_starts i > n := ⟨n + 2, segment_starts_gt_self' n⟩
  have h_le : Nat.find h_exist ≤ 2 ^ a + 1 := Nat.find_min' h_exist h_gt
  have h2 := Nat.sub_le_sub_right h_le 1
  rwa [Nat.add_sub_cancel] at h2

/-! ### Envelope case -/

/--
At an envelope `n` (where `is_envelope n`), `luby_via_segment n = S₂ n`.
-/
public theorem luby_via_segment_at_envelope (n : ℕ) (h : Luby.is_envelope n = true) :
    luby_via_segment n = Luby.S₂ n := by
  -- Case split: n = 0 vs n > 0
  obtain rfl | n_pos := Nat.eq_zero_or_pos n
  · -- n = 0: direct computation
    rw [luby_via_segment_zero_eq_one]
    -- Goal: 1 = Luby.S₂ 0
    -- S₂ 0 = 2 ^ ((0+1).size - 1) = 2 ^ (1.size - 1) = 2 ^ 0 = 1
    have h_size1 : (1 : ℕ).size = 1 := by
      have h1eq : (1 : ℕ) = 2 ^ 0 := by norm_num
      rw [h1eq, size_of_pow2_eq_self_add_one]; norm_num
    show 1 = Luby.S₂ 0
    unfold Luby.S₂
    rw [h_size1]; norm_num
  -- n > 0: extract j from envelope condition
  -- is_envelope n means S₂ (n + 2) = n + 2, i.e., 2^((n+3).size - 1) = n + 2
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
  -- Unfold luby_via_segment and S₂, reduce to showing exponents equal
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
  -- Goal: n - ∑ i ∈ range (2 ^ (j - 1) - 1), (trailing_zeros (i + 1) + 1) = j - 1
  -- Step 4: Compute the full sum ∑_{i<2^(j-1)} = 2^j - 1 via sum_of_trailing_zeros_prop
  have h_pow_eq : (2 : ℕ) ^ (j - 1) = 2 ^ ((2 ^ (j - 1)).size - 1) := by
    rw [size_of_pow2_eq_self_add_one]; simp
  have h_double : 2 * 2 ^ (j - 1) = 2 ^ j := by
    conv_rhs => rw [show j = (j - 1) + 1 from by omega]
    exact (pow_succ' 2 (j - 1)).symm
  have hsum_full : ∑ i ∈ range (2 ^ (j - 1)), (trailing_zeros (i + 1) + 1) = 2 ^ j - 1 := by
    have := sum_of_trailing_zeros_prop (2 ^ (j - 1)) h_pow_eq
    rwa [h_double] at this
  -- Step 5: Split off the last term: full_sum = partial_sum + trailing_zeros(2^(j-1)) + 1
  have h_split : 2 ^ (j - 1) = (2 ^ (j - 1) - 1) + 1 := by omega
  rw [h_split] at hsum_full
  rw [Finset.sum_range_succ] at hsum_full
  -- Simplify: 2^(j-1) - 1 + 1 = 2^(j-1)
  have h_restore : 2 ^ (j - 1) - 1 + 1 = 2 ^ (j - 1) := by omega
  rw [h_restore] at hsum_full
  -- trailing_zeros(2^(j-1)) = j - 1
  have h_tz : trailing_zeros (2 ^ (j - 1)) = j - 1 := trailing_zeros_prop3 (j - 1)
  rw [h_tz] at hsum_full
  -- hsum_full: partial_sum + (j - 1 + 1) = 2^j - 1, so partial_sum = 2^j - 1 - j
  rw [hn_eq]
  omega

/-! ### Non-envelope case -/

/--
For `¬is_envelope n`, the Luby recursion step preserves the offset within the covering segment.
-/
public theorem luby_via_segment_non_envelope (n : ℕ) (h : ¬(Luby.is_envelope n = true)) :
    luby_via_segment n = luby_via_segment (n + 1 - Luby.S₂ n) := by
  -- n ≥ 1 (since is_envelope 0 = true)
  have n_pos : n ≥ 1 := by
    by_contra hlt; push_neg at hlt
    have : n = 0 := by omega
    subst this
    have : Luby.is_envelope 0 = true := by simp [Luby.is_envelope, Luby.S₂, Nat.size, Nat.binaryRec]
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
    have : Luby.is_envelope n = true := by
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
      unfold Luby.is_envelope
      exact decide_eq_true_eq.mpr h_S2_eq
    exact h this
  have h_n_upper : n ≤ 2 ^ (a + 1) - 3 := by omega
  -- n' bounds
  have hn'_le : n' ≤ 2 ^ a - 2 := by simp only [hn'_def]; omega
  have hn'_add : n = n' + (2 ^ a - 1) := by simp only [hn'_def]; omega
  -- Goal: luby_via_segment n = luby_via_segment n'
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
  -- Key: segment_starts t = (2^a - 1) + segment_starts t'
  have h_shift : segment_starts t = (2 ^ a - 1) + segment_starts t' := by
    rw [ht_def, show a = (a - 1) + 1 from by omega]
    exact segment_starts_shift (a - 1) t' ht'_ge1 ht'_le
  -- segment_starts t' ≤ n' (from the Nat.find characterization)
  have h_over_n' : segmentIdOver n' = t' + 1 := by
    simp only [segmentIdCovering] at ht'_def; omega
  have h_starts_t'_le : segment_starts t' ≤ n' := by
    have h_lt : t' < segmentIdOver n' := by rw [h_over_n']; omega
    unfold segmentIdOver at h_lt
    have h_neg := Nat.find_min _ h_lt
    omega
  -- segment_starts t ≤ n
  have h_starts_t_le : segment_starts t ≤ n := by
    rw [h_shift, hn'_add]; omega
  -- segment_starts (t + 1) > n
  have h_starts_t1_gt : segment_starts (t + 1) > n := by
    have ht1_eq : t + 1 = 2 ^ (a - 1) + (t' + 1) := by omega
    rw [ht1_eq]
    -- segment_starts(segmentIdOver n') > n' by Nat.find_spec
    have h_exist' : ∃ i, segment_starts i > n' := ⟨n' + 2, segment_starts_gt_self' n'⟩
    have h_spec : segment_starts (t' + 1) > n' := by
      rw [← h_over_n']
      exact Nat.find_spec h_exist'
    obtain ht'1_le | ht'1_gt := le_or_gt (t' + 1) (2 ^ (a - 1))
    · -- Use shift identity
      have h_shift1 : segment_starts (2 ^ (a - 1) + (t' + 1)) =
          (2 ^ a - 1) + segment_starts (t' + 1) := by
        rw [show a = (a - 1) + 1 from by omega]
        exact segment_starts_shift (a - 1) (t' + 1) (by omega) ht'1_le
      rw [h_shift1, hn'_add]; omega
    · -- t' = 2^(a-1), so t + 1 = 2^a + 1
      have ht'_eq_bound : t' = 2 ^ (a - 1) := by omega
      have h_rw : 2 ^ (a - 1) + (t' + 1) = 2 ^ a + 1 := by
        rw [ht'_eq_bound]
        have : 2 ^ (a - 1) + 2 ^ (a - 1) = 2 ^ a := by
          rw [← two_pow_succ (a - 1), show a - 1 + 1 = a from by omega]
        omega
      rw [h_rw, segment_starts_pow2_add_one, hn'_add]; omega
  -- Prove segmentIdCovering n = t
  have h_seg_id : segmentIdCovering n = t := by
    suffices h_over_n : segmentIdOver n = t + 1 by
      simp [segmentIdCovering, h_over_n]
    simp only [segmentIdOver]
    have h_exist : ∃ i, segment_starts i > n := ⟨n + 2, segment_starts_gt_self' n⟩
    refine (Nat.find_eq_iff h_exist).mpr ⟨h_starts_t1_gt, ?_⟩
    intro j hj
    exact not_lt.mpr (Nat.le_trans (segment_starts_is_monotone (by omega : j ≤ t)) h_starts_t_le)
  -- Compute offsets: n - segment_starts t = n' - segment_starts t'
  have h_offset_eq : n - segment_starts t = n' - segment_starts t' := by
    rw [h_shift, hn'_add]; omega
  -- Conclude: both luby_via_segment values use the same exponent
  show luby_via_segment n = luby_via_segment n'
  rw [luby_via_segment_def n, luby_via_segment_def n']
  congr 1
  rw [h_seg_id, ofNat_start_eq t (by omega : t ≥ 1), ofNat_start_eq t' ht'_ge1]
  exact h_offset_eq

/-! ### Main theorem -/

/--
The Luby sequence computed via segment structure equals the recursive definition.

The proof is by strong induction on `n`, following the recursion of `Luby.luby`:
- **Envelope case** (`is_envelope n`): Both sides equal `S₂ n = 2^((n+1).size - 1)`.
  The covering segment has the right length (determined by `trailing_zeros`) so the
  power-of-two offset matches `S₂`.
- **Non-envelope case** (`¬is_envelope n`): The Luby recursion maps `n` to
  `n' = n + 1 - S₂ n`, which lies in the "first half" of the current envelope.
  By `segment_starts_shift`, the segment structure in the second half mirrors the first,
  preserving the offset. So `luby_via_segment n = luby_via_segment n'`, and by the
  inductive hypothesis `luby_via_segment n' = Luby.luby n'`.
-/
public theorem luby_via_segment_eq_luby (n : ℕ) : luby_via_segment n = Luby.luby n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [Luby.luby]
    split
    · -- Envelope case
      rename_i h_env
      exact luby_via_segment_at_envelope n h_env
    · -- Non-envelope case
      rename_i h_nenv
      -- Show n + 1 - S₂ n < n (for the inductive hypothesis)
      have n_pos : n ≥ 1 := by
        by_contra hlt; push_neg at hlt
        have : n = 0 := by omega
        subst this
        have : Luby.is_envelope 0 = true := by simp [Luby.is_envelope, Luby.S₂, Nat.size, Nat.binaryRec]
        exact h_nenv this
      have h_S2_ge2 : Luby.S₂ n ≥ 2 := S₂_ge_two' n (by omega)
      have h_dec : n + 1 - Luby.S₂ n < n := by omega
      rw [luby_via_segment_non_envelope n h_nenv]
      exact ih _ h_dec

end LubyState
