import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Basic
import Utils

structure LubyIterator where
  cycle : Nat
  -- segment is a local index within the current cycle
  segment : Nat

instance LubyIterator.inst : Inhabited LubyIterator := ⟨0, 0⟩

def LubyIterator.current_span (self : LubyIterator) : Nat := 2 ^ self.segment


def spanOfCycle (n : Nat) : Nat := match n with
  | 0     => 1
  | n + 1 => (trailing_zero n).succ

def LubyIterator.span_of_cycle (self : LubyIterator) : Nat := spanOfCycle self.cycle

#eval (default : LubyIterator)

def LubyIterator.next (self : LubyIterator) (repeating : Nat := 1) : LubyIterator :=
  match repeating with
  | 0     => self
  | r + 1 =>
    if _h : self.segment.succ = self.span_of_cycle
    then (LubyIterator.mk self.cycle.succ 0).next r
    else (LubyIterator.mk self.cycle self.segment.succ).next r

#eval scanList (·.next) (default : LubyIterator) 24 |>.map (·.current_span)
#eval scanList (·.next) (default : LubyIterator) 36 |>.map (fun i ↦ (i.cycle, i.segment, i.span_of_cycle, i.current_span))
#eval (default : LubyIterator).next 24 |>.current_span


/-
 - Sketch of proof on equality of iterator and Luby sequence:
 - show the isomorphism between the iterator and the Luby sequence
 - n : Nat → LubyIterator → next = Luby(n)
 - category? IsIso ?
-/

def LubyIterator.ofNat (n : Nat) : LubyIterator := (default : LubyIterator).next n

def S₁ (n: Nat) : Nat := n.succ.size.pred

#eval List.range 24 |>.map (fun k ↦ S₁ k)
#eval List.range 24 |>.map (fun k ↦ Luby.S₂ k)
#eval List.range 24 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

def LubyIterator.toNat (self : LubyIterator) : Nat :=
  (∑ k < self.cycle, spanOfCycle k) + self.segment

#eval scanList (·.next) (default : LubyIterator) 24 |>.map (·.toNat)

theorem LubyIterator0 : ∀ n : Nat, (LubyIterator.ofNat n).toNat = n := by
  intro n
  induction' n with n0 n
  {
    dsimp [LubyIterator.ofNat, LubyIterator.next]
    simp [default]
    simp [LubyIterator.toNat]
  }
  {
    simp [LubyIterator.ofNat, LubyIterator.next]
    let h01 : (default : LubyIterator).segment + 1 = (default : LubyIterator).span_of_cycle
        ∨ (default : LubyIterator).segment + 1 ≠ (default : LubyIterator).span_of_cycle := by
      exact eq_or_ne ((default : LubyIterator).segment + 1) (default : LubyIterator).span_of_cycle
    simp at *
    rcases h01 with t|f
    {
      simp [t]
      sorry
    }
    sorry
  }

theorem LubyIterator1 : ∀ n : Nat, (LubyIterator.ofNat n).next.toNat = n + 1 := by
  intro n
  induction' n with n0 n
  {
    dsimp [LubyIterator.ofNat, LubyIterator.next]
    simp [default, LubyIterator.span_of_cycle]
    sorry
   }
  sorry

theorem LubyIterator2 : ∀ n : Nat, (LubyIterator.ofNat n).current_span = Luby.luby n := by
  intro n
  sorry

theorem LubyIterator3 : ∀ n : Nat, LubyIterator.toNat (LubyIterator.ofNat n) = n := by
  sorry

instance : Coe Nat LubyIterator where
  coe n := LubyIterator.ofNat n
