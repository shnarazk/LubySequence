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

def S₂ (n: Nat) := 2^(n.succ.size - 1)
#eval List.range (16 : Nat) |>.map S₂

-- Checks if (k + 1) is one less than a power of two
def isSpecial (k : Nat) : Bool :=
  -- ((k + 2) &&& (k + 1)) == 0  -- k + 2 is a power of 2 ⇔ k + 1 = 2^i - 1
  S₂ (k + 2) == k + 2

#eval List.range 16 |>.map isSpecial -- |>.map (if · then "T" else "F")

/-
-- Returns the largest power of 2 less than or equal to (k + 1)
partial def largestPowerOf2LE₁ (k : Nat) : Nat :=
  let rec loop (i acc : Nat) :=
    if 2^i > k + 1 then acc else loop (i + 1) (2^i)
  loop 0 1

#eval List.range 16 |>.map largestPowerOf2LE₁ --

def largestPowerOf2LE (k : Nat) : Nat :=
  let rec loop (d i acc : Nat) :=
    match d with
    | 0 => acc
    | n + 1 => if 2^i > k + 1 then acc else loop n i.succ (2^i)
  loop k.bits.length.succ 0 1

#eval List.range 16 |>.map largestPowerOf2LE --
-/

theorem pow2_le_pow2 (a b : Nat) : a ≤ b → 2 ^ a ≤ 2 ^ b := by
  have : 2 > 0 := by exact Nat.zero_lt_two
  exact Nat.pow_le_pow_right this

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
    rw [←Nat.size]
    have (a b : Nat) : a ≤ b → a - 1 ≤ b - 1  := by
      apply fun a_1 ↦ Nat.sub_le_sub_right a_1 1
    apply this
    apply Nat.size_le_size
    omega
  }

theorem S₂_ge_two (k : Nat) (h : k > 0) : S₂ k ≥ 2 := by
  simp [S₂]
  rw [(by rfl : 2 = 2 ^1)]
  apply pow2_le_pow2
  have (a b c : Nat) (h : c ≤ b) : a ≤ b - c → a + c ≤ b := by
    apply Nat.add_le_of_le_sub h
  apply Nat.le_sub_of_add_le
  simp
  have : 2 ≤ (k + 1).size := by
    have h1 : k = 1 ∨ k > 1 := by exact LE.le.eq_or_gt h 
    rcases h1 with h1|h2
    { simp [h1, Nat.size, Nat.binaryRec] }
    {
      have h1 : 1 = (1 : Nat).size := by exact Eq.symm Nat.size_one -- apply?
      have h2 : 2 ≤ (2 : Nat).size := by simp [Nat.size, Nat.binaryRec]
      have h3 : 2 ≤ 1 + k := by omega
      have h4 : Nat.size 2 ≤ Nat.size (k + 1) := by
        simp only [Nat.add_comm k 1]
        exact Nat.size_le_size h3
      exact Nat.le_trans h2 h4
    }
  exact this

-- Well-founded version of the Luby sequence
partial def luby₁ : Nat → Nat
  | 0 => 1
  | k =>
    if isSpecial k then
      S₂ k
    else
     luby₁ (k + 1 - (S₂ k))


-- Well-founded version of the Luby sequence
def luby (n : ℕ) : Nat :=
  if n > 0 then
    if isSpecial n then S₂ n else luby (n + 1 - (S₂ n))
  else
    1
termination_by n
decreasing_by
  rcases n with z | k1 | k2
  { simp at * }
  { simp [S₂, Nat.size, Nat.binaryRec]  }
  {
    ring_nf at *
    simp at *
    have : 3 - S₂ (2 + k2) < 2 → 3 + k2 - S₂ (2 + k2) < 2 + k2 := by omega
    apply this
    have : 1 < S₂ (2 + k2) → 3 - S₂ (2 + k2) < 2 := by
      intro h
      have : S₂ (2 + k2) ≥ 2 := by exact S₂_ge_two (2 + k2) (by omega)
      omega
    apply this
    apply S₂_ge_two (2 + k2) (by omega)
  }

end Luby

-- 🧪 Test output
-- #eval List.range 16 |>.map Luby.luby
-- Output: [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1]
#eval List.range 16 |>.map Luby.isSpecial
#eval List.range 16 |>.map Nat.bits

structure LubyGenerator where
  c : Nat  -- index of cycle (an increasing sunsequence)
  i : Nat

def LubyGenerator.cycleBase (g : LubyGenerator) : Nat :=
   ∑ i < g.c, i

#eval (LubyGenerator.mk 4 0).cycleBase
