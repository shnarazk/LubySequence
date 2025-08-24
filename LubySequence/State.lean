import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import LubySequence.Basic
import Utils

structure LubyState where
  -- segment index (0-based)
  segIx : Nat
  -- local index within the current segment
  locIx : Nat

instance LubyState.inst : Inhabited LubyState := ⟨1, 0⟩
def LubyState.zero := (default : LubyState)

#check LubyState.zero

def LubyState.luby (self : LubyState) : Nat := 2 ^ self.locIx

@[simp]
def trailing_zero' (n : Nat) : Nat := match n with
  | 0     => 1
  | n + 1 => (trailing_zero n).succ

def LubyState.segment_height (self : LubyState) : Nat := trailing_zero self.segIx + 1

-- #eval LubyState.zero

def LubyState.is_segment_end (self : LubyState) : Bool :=
  self.locIx.succ = self.segment_height

def LubyState.next (self : LubyState) (repeating : Nat := 1) : LubyState :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let li := self.next r
    if li.is_segment_end -- li.locIx.succ = li.segment_height
    then LubyState.mk li.segIx.succ 0
    else LubyState.mk li.segIx li.locIx.succ

#eval scanList (·.next) LubyState.zero 24 |>.drop 3 |>.map (·.luby)
#eval scanList (·.next) LubyState.zero 36 |>.drop 3 |>.map (fun i ↦ (i.segIx, i.locIx, i.segment_height, i.luby))
#eval LubyState.zero.next 24 |>.luby

theorem LubyState.is_divergent (li : LubyState) : ¬(li.next = li) := by
  contrapose!
  intro t₀
  simp [LubyState.next]
  have tf : li.locIx + 1 = li.segment_height ∨ li.locIx + 1 ≠ li.segment_height := by
    exact eq_or_ne (li.locIx + 1) li.segment_height
  rcases tf with t|f
  {
    simp [LubyState.is_segment_end, t]
    have (a : LubyState) (h : ¬a.segIx = li.segIx) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg segIx a_1))
    simp [this]
  }
  {
    simp [LubyState.is_segment_end, f]
    have (a : LubyState) (h : ¬a.locIx = li.locIx) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg locIx a_1))
    simp [this]
  }

theorem LubyState.segIx_is_increasing : ∀ li : LubyState, li.next.segIx ≥ li.segIx := by
  intro li
  simp [LubyState.is_segment_end, LubyState.next]
  have : li.locIx + 1 = li.segment_height ∨ ¬(li.locIx + 1 = li.segment_height) := by
    exact eq_or_ne _ _
  rcases this with t|f
  { simp [t] }
  { simp [f] }

theorem LubyState.segIx_is_mono (n : Nat) : ∀ n' ≥ n, (LubyState.zero.next n').segIx ≥ (LubyState.zero.next n).segIx := by
  let cn := (LubyState.zero.next n).segIx
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
    have a2 : (zero.next (n + d)).next.segIx ≥ (zero.next (n + d)).segIx := by exact LubyState.segIx_is_increasing (zero.next (n + d))
    simp at a2
    exact le_trans dq a2
  }

theorem LubyState.segId_ge_one : ∀ n : Nat, (LubyState.zero.next n).segIx ≥ 1 := by
  intro n
  have p := LubyState.segIx_is_mono 0 n (Nat.zero_le n)
  have z : (zero.next 0).segIx = 1 := by
    simp [LubyState.zero, LubyState.next, default]
  simp [z] at p
  exact p

theorem LubyState.next0 (a : LubyState) : a.next 0 = a := by
  simp [LubyState.next]

theorem LubyState.congr (a b : LubyState) (h : a = b) : a.next = b.next := by
  exact congrFun (congrArg (@next) h) 1

theorem LubyState.segId0 {n : Nat} : n = 0 ↔ (LubyState.zero.next n).segIx = 1 := by
  constructor
  { intro h; rw [h]; exact rfl }
  {
    intro h
    by_contra x
    have base1 : (LubyState.zero.next 1).segIx = 2 := by
      simp [LubyState.zero, LubyState.next, LubyState.is_segment_end]
      simp [default, LubyState.segment_height, trailing_zero]
    have : n ≥ 1 → (LubyState.zero.next n).segIx ≥ 2 := by
      have sub : n ≥ 1 → (zero.next n).segIx ≥ (zero.next 1).segIx := by
        exact fun a ↦ LubyState.segIx_is_mono 1 n a
      simp [base1] at sub
      exact sub
    have np : n ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr x
    simp [np] at this
    grind
  }

theorem LubyState.next_assoc (li : LubyState) : ∀ n : Nat, (li.next n).next = li.next (n + 1) := by
  intro n
  induction' n with n hi
  { dsimp [LubyState.next] }
  {
    nth_rw 3 [LubyState.next]
    have tf : ((li.next (n + 1)).locIx.succ = (li.next (n + 1)).segment_height)
        ∨ ¬((li.next (n + 1)).locIx.succ = (li.next (n + 1)).segment_height) := by
      exact eq_or_ne _ _
    rcases tf with t|f
    {
      simp [LubyState.is_segment_end]
      have : (li.next (n + 1)).locIx.succ = (li.next (n + 1)).locIx + 1 := by exact rfl
      rw [this] at t
      simp only [t]
      simp
      have : (li.next (n + 1)).next = LubyState.mk ((li.next (n + 1)).segIx + 1) 0 := by
        nth_rw 1 [LubyState.next]
        simp [LubyState.is_segment_end]
        simp [LubyState.next0]
        exact t
      simp only [this]
    }
    {
      simp [LubyState.is_segment_end, f]
      have : (li.next (n + 1)).next = LubyState.mk ((li.next (n + 1)).segIx) ((li.next (n + 1)).locIx + 1) := by
        nth_rw 1 [LubyState.next]
        simp [LubyState.next0]
        simp [LubyState.is_segment_end]
        exact f
      simp only [this]
    }
  }

/-
 - Sketch of proof on equality of iterator and Luby sequence:
 - show the isomorphism between the iterator and the Luby sequence
 - n : Nat → LubyState → next = Luby(n)
 - category? IsIso ?
-/

def LubyState.ofNat (n : Nat) : LubyState := LubyState.zero.next n

def S₁ (n: Nat) : Nat := n.succ.size.pred

#eval List.range 24 |>.map (fun k ↦ S₁ k)
#eval List.range 24 |>.map (fun k ↦ Luby.S₂ k)
#eval List.range 24 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

-- @[simp]
def segIdToLastIndex (n : Nat) : Nat := match n with
  | 0     => 0
  | m + 1 => trailing_zero n + 1  + segIdToLastIndex m

def LubyState.toNat (self : LubyState) : Nat := match self.segIx with
  | 0 => 0
  | n + 1 => segIdToLastIndex n + self.locIx

#eval scanList (·.next) LubyState.zero 24 |>.map (·.toNat)

theorem LubyState.is_iso : ∀ n : Nat, (LubyState.ofNat n).toNat = n := by
  intro n
  change (LubyState.zero.next n).toNat = n
  induction' n with n hn
  { simp [LubyState.next, LubyState.zero, LubyState.toNat, segIdToLastIndex, default] }
  {
    simp [LubyState.toNat] at *
    split at hn
    {
      simp [←hn] at *
      expose_names
      have c := LubyState.segId_ge_one 0
      have c' : ¬(zero.next 0).segIx = 0 := by exact Nat.ne_zero_of_lt c
      exact absurd heq c'
/-
      split
      { next hh ou =>
        expose_names
        have c := LubyState.segId_ge_one 1
        have c' : ¬(zero.next 1).segIx = 0 := by exact Nat.ne_zero_of_lt c
        exact absurd ou c'
      }
      { next nh nn k =>
        export_names


        have c1 : LubyState.zero.next.segIx = 1 := by exact rfl
        have s1 : LubyState.zero.next.locIx = 0 := by exact rfl
        simp [c1] at k
        simp [k, segIdToLastIndex, s1]
      }
    -/
    }
    {
      expose_names
      split
      {
        next a b =>

        have c := LubyState.segId_ge_one (n + 1)
        have c' : ¬(zero.next (n + 1)).segIx = 0 := by exact Nat.ne_zero_of_lt c
        exact absurd b c'
      }
      {
        expose_names
        have : (LubyState.zero.next n).segIx - 1 = n_2 := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq)))
        simp only [←this] at *
        clear this
        have : (LubyState.zero.next (n + 1)).segIx - 1 = n_4 := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq_1)))
        simp only [←this] at *
        clear this
        have : LubyState.zero.next (n + 1) = (LubyState.zero.next n).next := by
          exact rfl
        simp [this] at *
        clear this heq heq_1
        let c := (LubyState.zero.next n).segIx
        have pc : c = value_of% c := rfl
        let s := (LubyState.zero.next n).locIx
        have ps : s = value_of% s := rfl
        simp [←pc, ←ps] at hn
        simp [LubyState.next]
        split
        {
          expose_names
          simp [LubyState.is_segment_end, ←ps] at h
          simp [←pc]
          rw [segIdToLastIndex.eq_def]
          cases cp : c with
          | zero =>
            simp [cp] at *
            have c1 := LubyState.segId_ge_one n
            have c2 : ¬0 = (zero.next n).segIx := by exact Nat.ne_of_lt c1
            exact absurd pc c2
          | succ m =>
            simp -- [cp]
            simp [cp] at hn
            have h' := Eq.symm h
            simp [LubyState.segment_height] at h'
            grind
        }
        { grind }
      }
    }
  }

theorem LubyState.next_is_succ :
    ∀ n : Nat, (LubyState.ofNat n).next.toNat = n + 1 := by
  intro n
  calc
    (LubyState.ofNat n).next.toNat = (LubyState.zero.next n).next.toNat := by exact rfl
    _ = (LubyState.zero.next (n + 1)).toNat := by exact rfl
    _ = n + 1 := by exact LubyState.is_iso (n + 1)

#eval List.range 28 |>.map (fun n ↦ ((LubyState.ofNat n).luby, Luby.luby n))

instance : Coe Nat LubyState where
  coe n := LubyState.ofNat n

theorem LubyState.LubyState_segment_prop1 {n : Nat}
    (h : (LubyState.ofNat n).is_segment_end = true) :
    Luby.is_segment_beg (n + 1) = true := by
  rw [Luby.is_segment_beg.eq_def]
  split
  { rfl }
  { rfl }
  { expose_names
    have : ¬Luby.is_envelope (n + 1) = true := by sorry
    split
    { expose_names; exact absurd h_1 this }
    { expose_names
      have : n + 1 + 1 - Luby.S₂ (n + 1) = 1 := by sorry
      simp [this]
      simp [Luby.is_segment_beg.eq_def] } }

theorem LubyState.LubyState_segment_prop2 {n : Nat} (h : Luby.is_segment_beg n) :
    (LubyState.ofNat n).luby = 1 := by

  sorry

theorem LubyState.LubyState_prop (n : Nat) :
    (LubyState.ofNat n).luby = if Luby.is_segment_beg n then 1 else 2 * (LubyState.ofNat (n - 1)).luby := by
  have segbeg0 : Luby.is_segment_beg 0 := by simp [Luby.is_segment_beg.eq_def]
  have segbeg1 : Luby.is_segment_beg 1 := by simp [Luby.is_segment_beg.eq_def]
  have defaultenv : (default : LubyState).is_segment_end =true := by
    simp [LubyState.is_segment_end, default, LubyState.segment_height, trailing_zero]
  induction' n with n hn
  { split
    { expose_names ; simp [ofNat, zero, default, LubyState.next, LubyState.luby] }
    { expose_names ; exact absurd segbeg0 h } }
  { split
    { expose_names ; exact LubyState_segment_prop2 h }
    { expose_names
      simp [LubyState.luby]
      have : 2 * 2 ^ (LubyState.ofNat n).locIx = 2 ^ ((LubyState.ofNat n).locIx + 1) := by
        exact Eq.symm Nat.pow_succ'
      simp [this]
      clear this
      have : LubyState.ofNat (n + 1) = (LubyState.ofNat n).next := by exact rfl
      simp [this, LubyState.next]
      clear this
      have c : ¬(LubyState.ofNat n).is_segment_end = true := by
        simp [LubyState.is_segment_end]
        simp [LubyState.segment_height]
        sorry
      split
      { expose_names
        exact absurd h_1 c }
      { simp }
    }
  }
