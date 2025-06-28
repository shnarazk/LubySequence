import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Basic

structure LubyGenerator where
  seg : Nat -- index of segment (an increasing subsequence)
  i   : Nat -- index in the current segment

def LubyGenerator.spanOfSegment (self : LubyGenerator) : Nat :=
  2 ^ self.seg

def LubyGenerator.segmentBase (self : LubyGenerator) : Nat :=
  ∑ i < self.seg, i

def trailing_zero (n : Nat) : Nat :=
  if h : n < 2
  then (1 - n)
  else if n % 2 = 0 then 1 + trailing_zero (n / 2) else 0

def trailing_one (n : Nat) : Nat :=
  if h : n < 2
  then n
  else if n % 2 = 0 then 0 else 1 + trailing_one (n / 2)

#eval List.range 9 |>.map trailing_zero
#eval List.range 9 |>.map trailing_one

def LubyGenerator.next (self : LubyGenerator) : Nat × LubyGenerator :=
  let i := trailing_one self.i
  let self' := if self.i = self.seg
    then LubyGenerator.mk (self.seg + 1) 0
    else LubyGenerator.mk self.seg (self.i + 1)
  (i, self')

#eval List.range 16 |>.foldl (fun lg _ ↦ let (i, g') := lg.snd.next; (lg.fst ++ [i], g')) (([] : List Nat), LubyGenerator.mk 0 0) |>.fst

#eval (LubyGenerator.mk 4 0).segmentBase
