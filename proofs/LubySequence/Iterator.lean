import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Basic

def trailing_zero (n : Nat) : Nat :=
  if h : n < 2
  then (1 - n)
  else if n % 2 = 0 then 1 + trailing_zero (n / 2) else 0

#eval List.range 9 |>.map trailing_zero

def trailing_one (n : Nat) : Nat :=
  if h : n < 2
  then n
  else if n % 2 = 0 then 0 else 1 + trailing_one (n / 2)

#eval List.range 9 |>.map trailing_one

def nexts {α : Type _} (f : α → α) (init : α) (n : Nat) (start : Bool := true) : List α :=
  match n with
  | 0      => []
  | n' + 1 => let nxt := f init; if start
    then init :: nxt :: nexts f nxt n' false
    else nxt :: nexts f nxt n' false

#eval nexts (· + 1) 10 8

structure LubyIterator where
  cycle_index : Nat
  segment_index_in_cycle : Nat

instance LubyIterator.inst : Inhabited LubyIterator :=
  ⟨0, 0⟩

def LubyIterator.current_span (self : LubyIterator) : Nat := 2 ^ self.segment_index_in_cycle
def LubyIterator.span_of_cycle (self : LubyIterator) : Nat := match self.cycle_index with
  | 0 => 1
  | n + 1 => (trailing_zero n).succ

#eval (default : LubyIterator)

def LubyIterator.next (self : LubyIterator) : LubyIterator :=
  if self.segment_index_in_cycle.succ = self.span_of_cycle
    then
      LubyIterator.mk self.cycle_index.succ 0
    else
      LubyIterator.mk self.cycle_index self.segment_index_in_cycle.succ

#eval nexts (·.next) (default : LubyIterator) 24 |>.map (·.current_span)
#eval nexts (·.next) (default : LubyIterator) 36 |>.map (fun i ↦ (i.cycle_index, i.segment_index_in_cycle, i.span_of_cycle, i.current_span))

/-
 - Sketch of proof on equality of iterator and Luby sequence:
 - show the isomorphism between the iterator and the Luby sequence
 - n : Nat → LubyIterator → next = Luby(n)
 - category? IsIso ?
-/

def LubyIterator.ofNat (n : Nat) : LubyIterator :=
  panic s!"Not implemented yet {n}"

def S₁ (n: Nat) : Nat := n.succ.size.pred

#eval List.range 24 |>.map (fun k ↦ S₁ k)
#eval List.range 24 |>.map (fun k ↦ Luby.S₂ k)
#eval List.range 24 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

def LubyIterator.toNat (self : LubyIterator) : Nat :=
  panic s!"Not implemented yet {self.cycle_index}"

theorem LubyIteratorIsIsomorphism : ∀ n : Nat, LubyIterator.toNat (LubyIterator.ofNat n) = n := by
  sorry
