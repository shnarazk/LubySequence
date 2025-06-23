import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits

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

-- Checks if (k + 1) is one less than a power of two
def isSpecial (k : Nat) : Bool :=
  ((k + 2) &&& (k + 1)) == 0  -- k + 2 is a power of 2 ⇔ k + 1 = 2^i - 1

#eval isSpecial 0  -- true because (0 + 1) is one less than 2^1
#eval isSpecial 1
#eval isSpecial 2  -- true because (2 + 1) is one less than 2^2
#eval isSpecial 6  -- true because (6 + 1) is one less than 2^3
#eval isSpecial 14  -- true because 14 is two less than 2^4

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

theorem twoLelargestPower2ofKGtZero (k : Nat) (h : k > 0) : largestPowerOf2LE k ≥ 2 := by
  sorry

-- Well-founded version of the Luby sequence
partial def luby₁ : Nat → Nat
  | 0 => 1
  | k =>
    if isSpecial k then
      largestPowerOf2LE k
    else
     luby₁ (k +1 - (largestPowerOf2LE k))


-- Well-founded version of the Luby sequence
def luby (n : ℕ) : Nat :=
  if n > 0 then
    if isSpecial n then largestPowerOf2LE n else luby (n + 1 - (largestPowerOf2LE n))
  else
    1
termination_by n
decreasing_by
  rcases n with z | k1 | k2
  { simp at * }
  { simp [largestPowerOf2LE, largestPowerOf2LE.loop] }
  {
    ring_nf at *
    simp at *
    have : largestPowerOf2LE (2 + k2) ≥ 2 := by
      apply twoLelargestPower2ofKGtZero
      exact Nat.pos_of_neZero (2 + k2)
    sorry
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
