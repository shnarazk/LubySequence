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
def LubyIterator.zero := (default : LubyIterator)

#check LubyIterator.zero

def LubyIterator.current_span (self : LubyIterator) : Nat := 2 ^ self.segment

@[simp]
def spanOfCycle (n : Nat) : Nat := match n with
  | 0     => 1
  | n + 1 => (trailing_zero n).succ

def LubyIterator.span_of_cycle (self : LubyIterator) : Nat := spanOfCycle self.cycle

#eval (default : LubyIterator)

def LubyIterator.next (self : LubyIterator) (repeating : Nat := 1) : LubyIterator :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let li := self.next r
    if li.segment.succ = li.span_of_cycle
    then LubyIterator.mk li.cycle.succ 0
    else LubyIterator.mk li.cycle li.segment.succ

#eval scanList (·.next) LubyIterator.zero 24 |>.map (·.current_span)
#eval scanList (·.next) LubyIterator.zero 36 |>.map (fun i ↦ (i.cycle, i.segment, i.span_of_cycle, i.current_span))
#eval (default : LubyIterator).next 24 |>.current_span

theorem LubyIterator.is_divergent (li : LubyIterator) : ¬(li.next = li) := by
  contrapose!
  intro t₀
  simp [LubyIterator.next]
  have tf : li.segment + 1 = li.span_of_cycle ∨ li.segment + 1 ≠ li.span_of_cycle := by
    exact eq_or_ne (li.segment + 1) li.span_of_cycle
  rcases tf with t|f
  {
    simp [t]
    have (a : LubyIterator) (h : ¬a.cycle = li.cycle) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg cycle a_1))
    simp [this]
  }
  {
    simp [f] 
    have (a : LubyIterator) (h : ¬a.segment = li.segment) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg segment a_1))
    simp [this]
  }

theorem LubyIterator.congr (a b : LubyIterator) (h : a = b) : a.next = b.next := by
  exact congrFun (congrArg (@next) h) 1

theorem LubyIterator.next_assoc (li : LubyIterator) : ∀ n : Nat, (li.next n).next = li.next (n + 1) := by
  intro n
  induction' n with n hi
  { dsimp [LubyIterator.next] }
  {
    nth_rw 3 [LubyIterator.next]
    have tf : ((li.next (n + 1)).segment.succ = (li.next (n + 1)).span_of_cycle)
        ∨ ¬((li.next (n + 1)).segment.succ = (li.next (n + 1)).span_of_cycle) := by
      exact eq_or_ne _ _
    rcases tf with t|f
    {
      simp only [t]
      simp
      have : LubyIterator.mk ((li.next (n + 1)).cycle + 1) 0 = (li.next (n + 1)).next := by
        sorry
      simp only [this]
    }
    {
      simp [f]
      sorry
    }
  }

/-
 - Sketch of proof on equality of iterator and Luby sequence:
 - show the isomorphism between the iterator and the Luby sequence
 - n : Nat → LubyIterator → next = Luby(n)
 - category? IsIso ?
-/

def LubyIterator.ofNat (n : Nat) : LubyIterator := (default : LubyIterator).next li

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
    {
      simp [f]

      sorry
    }
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

instance : Coe Nat LubyIterator where
  coe n := LubyIterator.ofNat n
