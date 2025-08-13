import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Basic
import Utils

structure LubyGenerator where
  -- segment index (0-based)
  segIx : Nat
  -- local index within the current segment
  locIx : Nat

instance LubyGenerator.inst : Inhabited LubyGenerator := ⟨0, 0⟩
def LubyGenerator.zero := (default : LubyGenerator)

#check LubyGenerator.zero

def LubyGenerator.luby (self : LubyGenerator) : Nat := 2 ^ self.locIx

@[simp]
def trailing_zero' (n : Nat) : Nat := match n with
  | 0     => 1
  | n + 1 => (trailing_zero n).succ

def LubyGenerator.segment_span (self : LubyGenerator) : Nat := trailing_zero' self.segIx

#eval LubyGenerator.zero

def LubyGenerator.next (self : LubyGenerator) (repeating : Nat := 1) : LubyGenerator :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let li := self.next r
    if li.locIx.succ = li.segment_span
    then LubyGenerator.mk li.segIx.succ 0
    else LubyGenerator.mk li.segIx li.locIx.succ

#eval scanList (·.next) LubyGenerator.zero 24 |>.drop 3 |>.map (·.luby)
#eval scanList (·.next) LubyGenerator.zero 36 |>.drop 3 |>.map (fun i ↦ (i.segIx, i.locIx, i.segment_span, i.luby))
#eval LubyGenerator.zero.next 24 |>.luby

theorem LubyGenerator.is_divergent (li : LubyGenerator) : ¬(li.next = li) := by
  contrapose!
  intro t₀
  simp [LubyGenerator.next]
  have tf : li.locIx + 1 = li.segment_span ∨ li.locIx + 1 ≠ li.segment_span := by
    exact eq_or_ne (li.locIx + 1) li.segment_span
  rcases tf with t|f
  {
    simp [t]
    have (a : LubyGenerator) (h : ¬a.segIx = li.segIx) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg segIx a_1))
    simp [this]
  }
  {
    simp [f]
    have (a : LubyGenerator) (h : ¬a.locIx = li.locIx) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg locIx a_1))
    simp [this]
  }

theorem LubyGenerator.segIx_is_increasing : ∀ li : LubyGenerator, li.next.segIx ≥ li.segIx := by
  intro li
  simp [LubyGenerator.next]
  have : li.locIx + 1 = li.segment_span ∨ ¬(li.locIx + 1 = li.segment_span) := by exact eq_or_ne _ _
  rcases this with t|f
  { simp [t] }
  { simp [f] }

theorem LubyGenerator.segIx_is_mono (n : Nat) : ∀ n' ≥ n, (LubyGenerator.zero.next n').segIx ≥ (LubyGenerator.zero.next n).segIx := by
  let cn := (LubyGenerator.zero.next n).segIx
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
    have a2 : (zero.next (n + d)).next.segIx ≥ (zero.next (n + d)).segIx := by exact LubyGenerator.segIx_is_increasing (zero.next (n + d))
    simp at a2
    exact le_trans dq a2
  }

theorem LubyGenerator.next0 (a : LubyGenerator) : a.next 0 = a := by
  simp [LubyGenerator.next]

theorem LubyGenerator.congr (a b : LubyGenerator) (h : a = b) : a.next = b.next := by
  exact congrFun (congrArg (@next) h) 1

theorem LubyGenerator.segId0 {n : Nat} : n = 0 ↔ (LubyGenerator.zero.next n).segIx = 0 := by
  constructor
  { intro h; rw [h]; exact rfl }
  {
    intro h
    by_contra x
    have base1 : (LubyGenerator.zero.next 1).segIx = 1 := by rfl
    have : n ≥ 1 → (LubyGenerator.zero.next n).segIx ≥ 1 := by
      have sub : n ≥ 1 → (zero.next n).segIx ≥ (zero.next 1).segIx := by exact fun a ↦ LubyGenerator.segIx_is_mono 1 n a
      exact sub
    have np : n ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr x
    simp [np] at this
    grind
  }

theorem LubyGenerator.next_assoc (li : LubyGenerator) : ∀ n : Nat, (li.next n).next = li.next (n + 1) := by
  intro n
  induction' n with n hi
  { dsimp [LubyGenerator.next] }
  {
    nth_rw 3 [LubyGenerator.next]
    have tf : ((li.next (n + 1)).locIx.succ = (li.next (n + 1)).segment_span)
        ∨ ¬((li.next (n + 1)).locIx.succ = (li.next (n + 1)).segment_span) := by
      exact eq_or_ne _ _
    rcases tf with t|f
    {
      simp only [t]
      simp
      have : (li.next (n + 1)).next = LubyGenerator.mk ((li.next (n + 1)).segIx + 1) 0 := by
        nth_rw 1 [LubyGenerator.next]
        simp [LubyGenerator.next0]
        exact t
      simp only [this]
    }
    {
      simp [f]
      have : (li.next (n + 1)).next = LubyGenerator.mk ((li.next (n + 1)).segIx) ((li.next (n + 1)).locIx + 1) := by
        nth_rw 1 [LubyGenerator.next]
        simp [LubyGenerator.next0]
        exact f
      simp only [this]
    }
  }

/-
 - Sketch of proof on equality of iterator and Luby sequence:
 - show the isomorphism between the iterator and the Luby sequence
 - n : Nat → LubyGenerator → next = Luby(n)
 - category? IsIso ?
-/

def LubyGenerator.ofNat (n : Nat) : LubyGenerator := LubyGenerator.zero.next n

def S₁ (n: Nat) : Nat := n.succ.size.pred

#eval List.range 24 |>.map (fun k ↦ S₁ k)
#eval List.range 24 |>.map (fun k ↦ Luby.S₂ k)
#eval List.range 24 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

-- @[simp]
def segIdToIndex (n : Nat) : Nat := match n with
  | 0     => 1
  | m + 1 => trailing_zero' n + segIdToIndex m

def LubyGenerator.toNat (self : LubyGenerator) : Nat := match self.segIx with
  | 0 => 0
  | n + 1 => segIdToIndex n + self.locIx

#eval scanList (·.next) LubyGenerator.zero 24 |>.map (·.toNat)

theorem LubyGenerator.is_iso : ∀ n : Nat, (LubyGenerator.ofNat n).toNat = n := by
  intro n
  change (LubyGenerator.zero.next n).toNat = n
  induction' n with n hn
  { simp [LubyGenerator.next, LubyGenerator.zero, LubyGenerator.toNat] }
  {
    simp [LubyGenerator.toNat] at *
    split at hn
    {
      simp [←hn] at *
      split
      { next hh ou => exact id (Eq.symm ou) }
      { next nh nn k =>
        have c1 : LubyGenerator.zero.next.segIx = 1 := by exact rfl
        have s1 : LubyGenerator.zero.next.locIx = 0 := by exact rfl
        simp [c1] at k
        simp [k, segIdToIndex, s1]
      }
    }
    {
      expose_names
      split
      {
        next a b =>
        have : ∀ n' ≥ 1, (LubyGenerator.zero.next n').segIx ≥ (LubyGenerator.zero.next 1).segIx := by
          exact fun n' a ↦ LubyGenerator.segIx_is_mono 1 n' a
        rcases this (n + 1) with g
        have : n + 1 ≥ 1 := by exact Nat.le_add_left 1 n
        simp [this] at g
        have : LubyGenerator.zero.next.segIx = 1 := by exact rfl
        simp [this] at g
        have : (LubyGenerator.zero.next (n + 1)).segIx ≠ 0 := by
          (expose_names; exact Nat.ne_zero_of_lt (this_1 (n + 1) this_2))
        exact absurd b this
      }
      {
        expose_names
        have : (LubyGenerator.zero.next n).segIx - 1 = n_2 := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq)))
        simp only [←this] at *
        clear this
        have : (LubyGenerator.zero.next (n + 1)).segIx - 1 = n_4 := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq_1)))
        simp only [←this] at *
        clear this
        have : LubyGenerator.zero.next (n + 1) = (LubyGenerator.zero.next n).next := by
          exact rfl
        simp [this] at *
        clear this heq heq_1
        let c := (LubyGenerator.zero.next n).segIx
        have pc : c = value_of% c := rfl
        let s := (LubyGenerator.zero.next n).locIx
        have ps : s = value_of% s := rfl
        simp [←pc, ←ps] at hn
        simp [LubyGenerator.next]
        split
        {
          expose_names
          simp [←ps] at h
          simp [←pc]
          rw [segIdToIndex.eq_def]
          cases cp : c with
          | zero =>
            simp [cp] at *
            have n0 := LubyGenerator.segId0.mpr (Eq.symm pc)
            exact n0
          | succ m =>
            simp -- [cp]
            simp [cp] at hn
            have h' := Eq.symm h
            simp [LubyGenerator.segment_span] at h'
            grind
        }
        { grind }
      }
    }
  }

theorem LubyGenerator.next_is_succ :
    ∀ n : Nat, (LubyGenerator.ofNat n).next.toNat = n + 1 := by
  intro n 
  calc
    (LubyGenerator.ofNat n).next.toNat = (LubyGenerator.zero.next n).next.toNat := by exact rfl
    _ = (LubyGenerator.zero.next (n + 1)).toNat := by exact rfl
    _ = n + 1 := by exact LubyGenerator.is_iso (n + 1)

#eval List.range 28 |>.map (fun n ↦ ((LubyGenerator.ofNat (n + 3)).luby, Luby.luby n))


instance : Coe Nat LubyGenerator where
  coe n := LubyGenerator.ofNat (n + 3)
