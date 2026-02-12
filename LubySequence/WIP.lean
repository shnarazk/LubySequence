module

import Mathlib.Tactic
public import LubySequence.Utils
public import LubySequence.Basic
-- public import LubySequence.Segment
public import LubySequence.SegmentSequence
public import LubySequence.State
public import LubySequence.TrailingZeros

namespace LubyState

open Nat

attribute [local simp] binaryRec

/-
#eval List.range 10
    |>.map (fun n ↦ 2 ^ (n + 1) - 2)
    |>.map (fun n ↦ (n, (Segment.segmentOver n).start - 1))
-/

theorem t20250913' : ∀ n > 0, n = 2 ^ n.size - 2 → (Segment.segmentOver n).start - 1 = n := by
  intro n n_gt_0 n2_is_pow2
  rw [Segment.segmentOver]
  rw [Segment.ofNat.eq_def]
  split <;> expose_names
  · rw [Segment.segmentIdOver] at heq
    simp [Segment.segment_starts] at heq
  · -- rw [Segment.segmentIdOver] at heq
    simp only [Segment.unfold_segment]
    replace heq : Segment.segmentIdOver n - 1 = t := by
      exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq)))
    --
    sorry

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
    refine sub_succ_lt_self (2 ^ (n + 1)) 1 ?_
    · exact one_lt_two_pow' n
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
