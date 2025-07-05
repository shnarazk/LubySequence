import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

namespace Luby

/-
  The Luby sequence is a sequence of natural numbers defined recursively.
  It is used in randomized algorithms and has applications in computer science.
  The sequence is defined as follows:

  L(k ≥ 1) = 2^(i-1)          if k = 2^i - 1 for some i ≥ 0,
           = L(k+1 - 2^(i-1)) if 2^(i-1) ≤ k ≤ 2^i - 1

If we want to start the sequence from 0, to make the mapping a total function:

  L(k ≥ 0) = 2^(i-1)          if k = 2^i - 2 for some i ≥ 0,
           = L(k+2 - 2^(i-1)) if 2^(i-1) ≤ k + 1 ≤ 2^i - 1

Or

  L(k ≥ 0) = 2^(I(k)-1)          if (k + 2) &&& (k + 1) = 0,
           = L(k+2 - 2^(I(k)-1)) otherwise
where
  I(n) = ⌈log₂(n+2)⌉
-/

/--
 - Basic relation between Nat and its binary representation.
 - A kind of ceiling function.
 -/
def S₂ (n : Nat) := 2^(n.succ.size - 1)
#eval List.range 24 |>.map S₂

theorem pow2_le_pow2 (a b : Nat) : a ≤ b → 2 ^ a ≤ 2 ^ b := by
  exact Nat.pow_le_pow_right (by grind : 2 > 0)

theorem S₂_ge_zero (n : Nat) : S₂ n ≥ 0 := by
  simp [S₂]

theorem S₂_is_mono : ∀ n ≥ 0, S₂ n ≤ S₂ (n + 1) := by
  intro i n0
  induction' i with a h
  { simp [S₂, Nat.size, Nat.binaryRec] }
  {
    simp at h
    dsimp [S₂, Nat.size]
    apply pow2_le_pow2
    rw [←Nat.size]
    apply fun x ↦ Nat.sub_le_sub_right x 1
    apply Nat.size_le_size
    grind
  }

theorem S₂_ge_two (k : Nat) (h : k > 0) : S₂ k ≥ 2 := by
  simp [S₂]
  rw [(by rfl : 2 = 2 ^1)]
  apply pow2_le_pow2
  apply Nat.le_sub_of_add_le
  simp
  have : 2 ≤ (k + 1).size := by
    have h1 : k = 1 ∨ k > 1 := by exact LE.le.eq_or_gt h
    rcases h1 with h1|h2
    { simp [h1, Nat.size, Nat.binaryRec] }
    {
      have h1 : 1 = (1 : Nat).size := by exact Eq.symm Nat.size_one
      have h2 : 2 ≤ (2 : Nat).size := by simp [Nat.size, Nat.binaryRec]
      have h3 : 2 ≤ 1 + k := by grind
      have h4 : Nat.size 2 ≤ Nat.size (k + 1) := by
        simp only [Nat.add_comm k 1]
        exact Nat.size_le_size h3
      exact Nat.le_trans h2 h4
    }
  exact this

theorem power2_ge_linear (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction' n with k h
  { simp }
  {
    have h2 : 2 ^(k + 1) = 2^k * 2 := by omega
    rw [h2]
    have t1 : k + 1 + 1 ≤ 2 ^ k + 1 := by omega
    have t2 : 2 ^ k + 1 ≤ 2 ^ k + 2 ^ k := by
      have : 1 ≤ 2 ^ k := by omega
      exact Nat.add_le_add_iff_left.mpr this
    have (k : Nat) : k + k = k * 2 := by exact Eq.symm (Nat.mul_two k)
    rw [this] at t2
    exact Nat.le_trans t1 t2
  }

-- Well-founded version of the Luby sequence
def luby (n : ℕ) : Nat :=
  if n > 0 then
    if S₂ (n + 2) = n + 2 then S₂ n else luby (n + 1 - (S₂ n))
  else
    1
termination_by n
decreasing_by
  rcases n with z | k1 | k2
  { simp at * }
  { simp [S₂, Nat.size, Nat.binaryRec] }
  {
    ring_nf at *
    simp at *
    have : 3 - S₂ (2 + k2) < 2 → 3 + k2 - S₂ (2 + k2) < 2 + k2 := by omega
    apply this
    have : 1 < S₂ (2 + k2) → 3 - S₂ (2 + k2) < 2 := by
      intro h
      have : S₂ (2 + k2) ≥ 2 := by exact S₂_ge_two (2 + k2) (by grind)
      grind
    apply this
    apply S₂_ge_two (2 + k2) (by grind)
  }

end Luby

-- 🧪 Test output
#eval List.range 24 |>.map Luby.luby
-- Output: [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1]
