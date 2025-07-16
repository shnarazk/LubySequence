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

#eval LubyIterator.zero

def LubyIterator.next (self : LubyIterator) (repeating : Nat := 1) : LubyIterator :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let li := self.next r
    if li.segment.succ = li.span_of_cycle
    then LubyIterator.mk li.cycle.succ 0
    else LubyIterator.mk li.cycle li.segment.succ

#eval scanList (·.next) LubyIterator.zero 24 |>.drop 3 |>.map (·.current_span)
#eval scanList (·.next) LubyIterator.zero 36 |>.drop 3 |>.map (fun i ↦ (i.cycle, i.segment, i.span_of_cycle, i.current_span))
#eval LubyIterator.zero.next 24 |>.current_span

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

theorem LubyIterator.cycle_is_increasing : ∀ li : LubyIterator, li.next.cycle ≥ li.cycle := by
  intro li
  simp [LubyIterator.next]
  have : li.segment + 1 = li.span_of_cycle ∨ ¬(li.segment + 1 = li.span_of_cycle) := by exact eq_or_ne _ _
  rcases this with t|f
  { simp [t] }
  { simp [f] }

theorem LubyIterator.cycle_is_mono (n : Nat) : ∀ n' ≥ n, (LubyIterator.zero.next n').cycle ≥ (LubyIterator.zero.next n).cycle := by
  let cn := (LubyIterator.zero.next n).cycle
  have cp : cn = value_of% cn := rfl
  intro n' np
  let d := n' - n 
  have dp : d = value_of% d := rfl
  have dp' : n' = n + d := by exact Eq.symm (Nat.add_sub_of_le np)
  simp [dp']
  induction' d with d dq
  { simp }
  {
    have a1 : zero.next (n + d + 1) = (zero.next (n + d)).next := by exact rfl
    have a2 : (zero.next (n + d)).next.cycle ≥ (zero.next (n + d)).cycle := by exact cycle_is_increasing (zero.next (n + d))
    simp at a2
    exact le_trans dq a2
  }

theorem LubyIterator.next0 (a : LubyIterator) : a.next 0 = a := by
  simp [LubyIterator.next]

theorem LubyIterator.congr (a b : LubyIterator) (h : a = b) : a.next = b.next := by
  exact congrFun (congrArg (@next) h) 1

theorem LubyIterator.cycle0 {n : Nat} : n = 0 ↔ (LubyIterator.zero.next n).cycle = 0 := by
  constructor
  { intro h; rw [h]; exact rfl }
  {
    intro h
    by_contra x
    have base1 : (LubyIterator.zero.next 1).cycle = 1 := by rfl
    have : n ≥ 1 → (LubyIterator.zero.next n).cycle ≥ 1 := by
      have sub : n ≥ 1 → (zero.next n).cycle ≥ (zero.next 1).cycle := by exact fun a ↦ cycle_is_mono 1 n a
      exact sub 
    have np : n ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr x
    simp [np] at this
    grind
  }

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
      have : (li.next (n + 1)).next = LubyIterator.mk ((li.next (n + 1)).cycle + 1) 0 := by
        nth_rw 1 [LubyIterator.next]
        simp [LubyIterator.next0]
        exact t
      simp only [this]
    }
    {
      simp [f]
      have : (li.next (n + 1)).next = LubyIterator.mk ((li.next (n + 1)).cycle) ((li.next (n + 1)).segment + 1) := by
        nth_rw 1 [LubyIterator.next]
        simp [LubyIterator.next0]
        exact f
      simp only [this]
    }
  }

/-
 - Sketch of proof on equality of iterator and Luby sequence:
 - show the isomorphism between the iterator and the Luby sequence
 - n : Nat → LubyIterator → next = Luby(n)
 - category? IsIso ?
-/

def LubyIterator.ofNat (n : Nat) : LubyIterator := LubyIterator.zero.next n

def S₁ (n: Nat) : Nat := n.succ.size.pred

#eval List.range 24 |>.map (fun k ↦ S₁ k)
#eval List.range 24 |>.map (fun k ↦ Luby.S₂ k)
#eval List.range 24 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

-- @[simp]
def cycleToNat (n : Nat) : Nat := match n with
  | 0     => 1
  | m + 1 => spanOfCycle n + cycleToNat m

def LubyIterator.toNat (self : LubyIterator) : Nat := match self.cycle with
  | 0 => 0
  | n + 1 => cycleToNat n + self.segment

#eval scanList (·.next) LubyIterator.zero 24 |>.map (·.toNat)

theorem LubyIterator0 : ∀ n : Nat, (LubyIterator.ofNat n).toNat = n := by
  intro n
  change (LubyIterator.zero.next n).toNat = n
  induction' n with n hn
  { simp [LubyIterator.next, LubyIterator.zero, LubyIterator.toNat] }
  {
    simp [LubyIterator.toNat] at *
    split at hn
    {
      simp [←hn] at *
      split
      { next hh ou => exact id (Eq.symm ou) }
      { next nh nn k =>
        have c1 : LubyIterator.zero.next.cycle = 1 := by exact rfl
        have s1 : LubyIterator.zero.next.segment = 0 := by exact rfl
        simp [c1] at k
        simp [k, cycleToNat, s1]
      }
    }
    {
      expose_names
      split
      {
        next a b =>
        have : ∀ n' ≥ 1, (LubyIterator.zero.next n').cycle ≥ (LubyIterator.zero.next 1).cycle := by
          exact fun n' a ↦ LubyIterator.cycle_is_mono 1 n' a
        rcases this (n + 1) with g
        have : n + 1 ≥ 1 := by exact Nat.le_add_left 1 n
        simp [this] at g
        have : LubyIterator.zero.next.cycle = 1 := by exact rfl
        simp [this] at g
        have : (LubyIterator.zero.next (n + 1)).cycle ≠ 0 := by
          (expose_names; exact Nat.ne_zero_of_lt (this_1 (n + 1) this_2))
        exact absurd b this
      }
      {
        expose_names
        have : (LubyIterator.zero.next n).cycle - 1 = n_2 := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq)))
        simp only [←this] at *
        clear this
        have : (LubyIterator.zero.next (n + 1)).cycle - 1 = n_4 := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq_1)))
        simp only [←this] at *
        clear this
        have : LubyIterator.zero.next (n + 1) = (LubyIterator.zero.next n).next := by exact rfl
        simp [this] at *
        clear this heq heq_1
        let c := (LubyIterator.zero.next n).cycle
        have pc : c = value_of% c := rfl
        let s := (LubyIterator.zero.next n).segment
        have ps : s = value_of% s := rfl
        simp [←pc, ←ps] at hn 
        simp [LubyIterator.next]
        split
        {
          expose_names
          simp [←ps] at h 
          simp [←pc]
          rw [cycleToNat.eq_def]
          cases cp : c with
          | zero =>
            simp [cp] at *
            have n0 := LubyIterator.cycle0.mpr (Eq.symm pc)
            exact n0
          | succ m =>
            simp -- [cp]
            simp [cp] at hn
            -- let t := (LubyIterator.zero.next n).span_of_cycle 
            -- have tp : t = value_of% t := rfl
            -- simp [←tp] at h
            have h' := Eq.symm h
            simp [LubyIterator.span_of_cycle] at h'
            grind
        }
        { grind }
      }
    }
  }

theorem LubyIterator1 : ∀ n : Nat, (LubyIterator.ofNat n).next.toNat = n + 1 := by
  intro n
  calc
    (LubyIterator.ofNat n).next.toNat = (LubyIterator.zero.next n).next.toNat := by exact rfl
    _ = (LubyIterator.zero.next (n + 1)).toNat := by exact rfl
    _ = n + 1 := by exact LubyIterator0 (n + 1)

theorem LubyIterator2 : ∀ n : Nat, (LubyIterator.ofNat n).current_span = Luby.luby n := by
  intro n
  induction' n using Nat.strong_induction_on with n hn
  {
    simp [LubyIterator.current_span]
    rw [Luby.luby]
  
    sorry
  }

instance : Coe Nat LubyIterator where
  coe n := LubyIterator.ofNat n
