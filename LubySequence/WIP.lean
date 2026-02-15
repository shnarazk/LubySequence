module

public import Mathlib.Tactic
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

/--
`is_envelope n` means `n + 2` is a power of 2: `n + 2 = 2 ^ ((n+2).size - 1)`.
We derive this from the definition of `is_envelope`.
-/
private theorem is_envelope_iff_pow2 (n : ℕ) :
    Luby.is_envelope n = true → n + 2 = 2 ^ ((n + 2).size - 1) := by
  intro h
  simp [Luby.is_envelope, Luby.S₂] at h
  -- h : 2 ^ ((n + 3).size - 1) = n + 2
  -- We need: n + 2 = 2 ^ ((n + 2).size - 1)
  -- Since n + 2 = 2^j for some j, (n+2).size = j+1, so (n+2).size - 1 = j
  -- And (n + 3) = 2^j + 1, (n+3).size = j+1 (by size_add), so (n+3).size - 1 = j
  set j := (n + 3).size - 1 with hj_def
  have h_eq : n + 2 = 2 ^ j := by omega
  have hj_pos : j ≥ 1 := by
    by_contra hlt; push_neg at hlt
    have : j = 0 := by omega
    rw [this] at h_eq; omega
  -- Now show (n+2).size - 1 = j
  have h_n2_size : (n + 2).size = j + 1 := by
    rw [h_eq]; exact size_of_pow2_eq_self_add_one j
  rw [h_n2_size]; simp; exact h_eq

/--
The Luby sequence computed via segment structure equals the recursive definition.
-/
public theorem luby_of_next_of_envelop_is_luby (n : ℕ) : luby_via_segment n = Luby.luby n := by
  sorry

end LubyState
