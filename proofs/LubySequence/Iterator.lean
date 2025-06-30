import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Basic

structure LubyIterator where
  cycle_index : Nat
  span_of_cycle : Nat
  segment_index_in_cycle : Nat

instance LubyIterator.inst : Inhabited LubyIterator :=
  ⟨0, 1, 1⟩

#eval (default : LubyIterator)

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

def LubyIterator.next (self : LubyIterator) : Nat × LubyIterator :=
  if self.segment_index_in_cycle = self.span_of_cycle
    then
      ( 1,
        LubyIterator.mk
          self.cycle_index.succ
          (trailing_zero self.cycle_index.succ).succ
          1)
    else
      ( 2^self.segment_index_in_cycle,
        LubyIterator.mk
          self.cycle_index
          self.span_of_cycle
          self.segment_index_in_cycle.succ)

#eval List.range 16 |>.foldl (fun lg _ ↦ let (i, g') := lg.snd.next; (lg.fst ++ [i], g')) (([] : List Nat), (default : LubyIterator)) |>.fst
#eval List.range 16 |>.foldl (fun lg _ ↦ match lg with | [] => [] | i :: _ => i.next.snd :: lg) [(default : LubyIterator)] |>.reverse |>.map (fun i ↦ (i.cycle_index, i.segment_index_in_cycle))

/-
 - Sketch of proof on equality of iterator and Luby sequence:
 - show the isomorphism between the iterator and the Luby sequence
 - n : Nat → LubyIterator → next = Luby(n)
 - category? IsIso ?
-/

def LubyIterator.ofNat (n : Nat) : LubyIterator :=
  panic s!"Not implemented yet {n}"

def S₁ (n: Nat) : Nat := n.succ.size.pred

#eval List.range 16 |>.map (fun k ↦ S₁ k)
#eval List.range 16 |>.map (fun k ↦ Luby.S₂ k)
#eval List.range 16 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

def LubyIterator.toNat (self : LubyIterator) : Nat :=
  panic s!"Not implemented yet {self.cycle_index}"

theorem LubyIteratorIsIsomorphism : ∀ n : Nat, LubyIterator.toNat (LubyIterator.ofNat n) = n := by
  sorry
