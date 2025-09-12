import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Finset.Basic
import LubySequence.Basic
import Utils
open Finset

structure LubyState where
  -- segment index (0-based)
  segIx : ℕ
  -- local index within the current segment
  locIx : ℕ

instance LubyState.inst : Inhabited LubyState := ⟨1, 0⟩
instance LubyState.repl : Repr LubyState where
  reprPrec s _ := "LubyState(" ++ toString s.segIx ++ ", " ++ toString s.locIx ++ ")"

def LubyState.zero := (default : LubyState)

-- #check LubyState.zero
-- #eval LubyState.zero

def LubyState.luby (self : LubyState) : ℕ := 2 ^ self.locIx
def LubyState.segment_height (self : LubyState) : ℕ := trailing_zeros self.segIx + 1
def LubyState.is_segment_beg (self : LubyState) : Bool := self.locIx = 0
def LubyState.is_segment_end (self : LubyState) : Bool := self.locIx.succ = self.segment_height

def LubyState.next (self : LubyState) (repeating : ℕ := 1) : LubyState :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let li := self.next r
    if li.is_segment_end
    then LubyState.mk li.segIx.succ 0
    else LubyState.mk li.segIx li.locIx.succ

#eval LubyState.zero.next 2
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
  · simp [LubyState.is_segment_end, t]
    have (a : LubyState) (h : ¬a.segIx = li.segIx) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg segIx a_1))
    simp [this]
  · simp [LubyState.is_segment_end, f]
    have (a : LubyState) (h : ¬a.locIx = li.locIx) : ¬a = li := by
      exact fun a_1 ↦ t₀ (h (congrArg locIx a_1))
    simp [this]

theorem LubyState.segIx_is_increasing : ∀ li : LubyState, li.next.segIx ≥ li.segIx := by
  intro li
  simp [LubyState.is_segment_end, LubyState.next]
  have : li.locIx + 1 = li.segment_height ∨ ¬(li.locIx + 1 = li.segment_height) := by
    exact eq_or_ne _ _
  rcases this with p|p <;> simp [p]

theorem LubyState.segIx_is_mono (n : ℕ) : ∀ n' ≥ n,
    (LubyState.zero.next n').segIx ≥ (LubyState.zero.next n).segIx := by
  let cn := (LubyState.zero.next n).segIx
  have cp : cn = value_of% cn := rfl
  intro n' np
  let d := n' - n
  have dp : d = value_of% d := rfl
  have dp' : n' = n + d := by exact Eq.symm (Nat.add_sub_of_le np)
  simp [dp']
  induction d with
  | zero => simp
  | succ d dq =>
    have a1 : zero.next (n + d + 1) = (zero.next (n + d)).next := by exact rfl
    have a2 : (zero.next (n + d)).next.segIx ≥ (zero.next (n + d)).segIx := by
      exact LubyState.segIx_is_increasing (zero.next (n + d))
    simp at a2
    exact le_trans dq a2

theorem LubyState.segId_ge_one : ∀ n : ℕ, (LubyState.zero.next n).segIx ≥ 1 := by
  intro n
  have p := LubyState.segIx_is_mono 0 n (Nat.zero_le n)
  have z : (zero.next 0).segIx = 1 := by simp [LubyState.zero, LubyState.next, default]
  simp [z] at p
  exact p

theorem LubyState.next0 (a : LubyState) : a.next 0 = a := by simp [LubyState.next]

theorem LubyState.congr (a b : LubyState) (h : a = b) : a.next = b.next := by
  exact congrFun (congrArg (@next) h) 1

theorem LubyState.segId0 {n : ℕ} : n = 0 ↔ (LubyState.zero.next n).segIx = 1 := by
  constructor
  · intro h; rw [h]; exact rfl
  · intro h
    by_contra x
    have base1 : (LubyState.zero.next 1).segIx = 2 := by
      simp [LubyState.zero, LubyState.next, LubyState.is_segment_end]
      simp [default, LubyState.segment_height, trailing_zeros]
    have np : n ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr x
    have : (LubyState.zero.next n).segIx ≥ 2 := by
      have sub : (zero.next n).segIx ≥ (zero.next 1).segIx := by exact LubyState.segIx_is_mono 1 n np
      simp [base1] at sub
      exact sub
    grind

theorem LubyState.next_assoc (li : LubyState) : ∀ n : ℕ, (li.next n).next = li.next (n + 1) := by
  intro n
  induction n with
  | zero => dsimp [LubyState.next]
  | succ n hi =>
    nth_rw 3 [LubyState.next]
    have tf : (li.next (n + 1)).locIx.succ = (li.next (n + 1)).segment_height
        ∨ ¬(li.next (n + 1)).locIx.succ = (li.next (n + 1)).segment_height := by
      exact eq_or_ne _ _
    rcases tf with t|f
    · simp [LubyState.is_segment_end]
      have : (li.next (n + 1)).locIx.succ = (li.next (n + 1)).locIx + 1 := by exact rfl
      rw [this] at t
      simp only [t]
      simp
      have : (li.next (n + 1)).next = LubyState.mk ((li.next (n + 1)).segIx + 1) 0 := by
        nth_rw 1 [LubyState.next]
        simp [LubyState.is_segment_end, LubyState.next0]
        exact t
      simp only [this]
    · simp [LubyState.is_segment_end, f]
      have : (li.next (n + 1)).next = LubyState.mk ((li.next (n + 1)).segIx) ((li.next (n + 1)).locIx + 1) := by
        nth_rw 1 [LubyState.next]
        simp [LubyState.next0, LubyState.is_segment_end]
        exact f
      simp only [this]

def LubyState.ofNat (n : ℕ) : LubyState := LubyState.zero.next n

theorem LubyState.ofNat_dist (a b : ℕ) : LubyState.ofNat (a + b) = (LubyState.ofNat a).next b := by
  induction b with
  | zero => simp [LubyState.next]
  | succ b hb =>
    have t1 : a + (b + 1) = a + b + 1 := by grind
    simp [t1]
    have t2 : ofNat (a + b + 1) = (ofNat (a + b)).next := by exact rfl
    simp [t2, hb]
    exact rfl

def S₁ (n: ℕ) : ℕ := n.succ.size.pred

#eval List.range 24 |>.map (fun k ↦ S₁ k)
#eval List.range 24 |>.map (fun k ↦ Luby.S₂ k)
#eval List.range 24 |>.map (fun k ↦ (S₁ k, k + 2 - Luby.S₂ k))

-- @[simp]
def segIdToLastIndex (n : ℕ) : ℕ := match n with
  | 0     => 0
  | m + 1 => trailing_zeros n + 1  + segIdToLastIndex m

def LubyState.toNat (self : LubyState) : ℕ := match self.segIx with
  | 0 => 0
  | n + 1 => segIdToLastIndex n + self.locIx

#eval scanList (·.next) LubyState.zero 24 |>.map (·.toNat)

theorem LubyState.is_iso : ∀ n : ℕ, (LubyState.ofNat n).toNat = n := by
  intro n
  change (LubyState.zero.next n).toNat = n
  induction n with
  | zero =>
   simp [LubyState.next, LubyState.zero, LubyState.toNat, segIdToLastIndex, default]
  | succ n hn =>
    simp [LubyState.toNat] at *
    split at hn
    · simp [←hn] at *
      expose_names
      have c := LubyState.segId_ge_one 0
      have c' : ¬(zero.next 0).segIx = 0 := by exact Nat.ne_zero_of_lt c
      exact absurd heq c'
    · expose_names
      split
      · next a b =>
        have c := LubyState.segId_ge_one (n + 1)
        have c' : ¬(zero.next (n + 1)).segIx = 0 := by exact Nat.ne_zero_of_lt c
        exact absurd b c'
      · expose_names
        have : (LubyState.zero.next n).segIx - 1 = m := by
          exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm heq)))
        simp only [←this] at *
        clear this
        have : (LubyState.zero.next (n + 1)).segIx - 1 = m_1 := by
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
        · expose_names
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
        · grind

theorem LubyState.next_is_succ : ∀ n : ℕ, (LubyState.ofNat n).next.toNat = n + 1 := by
  intro n
  calc
    (LubyState.ofNat n).next.toNat = (LubyState.zero.next n).next.toNat := by exact rfl
    _ = (LubyState.zero.next (n + 1)).toNat := by exact rfl
    _ = n + 1 := by exact LubyState.is_iso (n + 1)

#eval List.range 28 |>.map (fun n ↦ ((LubyState.ofNat n).luby, Luby.luby n))

instance : Coe ℕ LubyState where
  coe n := LubyState.ofNat n

theorem LubyState.LubyState_segment_prop1 {n : ℕ}
    (h : (LubyState.ofNat n).is_segment_end = true) :
    (LubyState.ofNat (n + 1)).is_segment_beg = true := by
  rw [LubyState.is_segment_beg]
  have p1 : ofNat (n + 1) = (ofNat n).next := by exact rfl
  simp [LubyState.next] at p1
  split at p1
  · simp at *
    have : (ofNat (n + 1)).locIx = 0 := by grind
    exact this
  · expose_names; exact absurd h h_1

theorem LubyState.LubyState_segment_prop2 {n : ℕ} (h : LubyState.is_segment_beg n) :
    (LubyState.ofNat n).luby = 1 := by
  simp [LubyState.is_segment_beg] at h
  simp [LubyState.luby]
  exact h

theorem LubyState.LubyState_prop (n : ℕ) :
    (LubyState.ofNat n).luby = if LubyState.is_segment_beg n then 1 else 2 * (LubyState.ofNat (n - 1)).luby := by
  have segbeg0 : Luby.is_segment_beg 0 := by simp [Luby.is_segment_beg.eq_def]
  have segbeg1 : Luby.is_segment_beg 1 := by simp [Luby.is_segment_beg.eq_def]
  have defaultenv : (default : LubyState).is_segment_end =true := by
    simp [LubyState.is_segment_end, default, LubyState.segment_height, trailing_zeros]
  split
  · expose_names ; exact LubyState_segment_prop2 h
  · expose_names
    have n0 : n > 0 := by
      by_contra x
      have n0 : n = 0 := by exact Nat.eq_zero_of_not_pos x
      have c : (ofNat n).is_segment_beg = true := by
        simp [n0, ofNat, zero, default, LubyState.next, LubyState.is_segment_beg]
      exact absurd c h
    have t1 : ofNat (n - 1 + 1) = (ofNat (n - 1)).next := by exact rfl
    have t2 : n - 1 + 1 = n := by exact Nat.sub_add_cancel n0
    simp [t2] at t1
    simp [t1, LubyState.next]
    have t3 : ¬(ofNat (n - 1)).is_segment_end = true := by
      by_contra x
      have c : (ofNat (n - 1 + 1)).is_segment_beg  := by exact LubyState_segment_prop1 x
      have t1 : n - 1 + 1 = n := by grind
      simp [t1] at c
      exact absurd c h
    split
    · expose_names ; exact absurd h_1 t3
    · expose_names ; simp [LubyState.luby] ; exact Nat.pow_succ'

def LubyState.toSegIx (n segIx sum : ℕ) : ℕ :=
  let len := trailing_zeros segIx + 1
  if hn : n <= len
  then segIx
  else
    have len1 : 1 ≤ len := by exact Nat.le_add_left 1 (trailing_zeros segIx)
    have n0 : 0 < n := by
      have : len < n := by exact Nat.gt_of_not_le hn
      exact Nat.zero_lt_of_lt this
    have n_is_decreasing : n - len < n := by
      have t1 : 0 < len := by exact Nat.zero_lt_succ (trailing_zeros segIx)
      have t2 : len < n := by exact Nat.gt_of_not_le hn
      exact Nat.sub_lt n0 t1
    LubyState.toSegIx (n - len) (segIx + 1) (sum + len)

def LubyState.sumOfSegmentHeights : ℕ → ℕ
  | 0     => 0
  | n + 1 => trailing_zeros (n + 1) + LubyState.sumOfSegmentHeights n

def LubyState.toLocIx (n : ℕ) : ℕ := n - LubyState.sumOfSegmentHeights n

def LubyState.next_in_segment (s : LubyState) (d : ℕ) : LubyState := LubyState.mk s.segIx (s.locIx + d)

theorem LubyState.next_in_segment_is_additive {s : LubyState} {d : ℕ} :
    ∀ d' < d, 0 < d' → s.next_in_segment d' = (s.next_in_segment (d' - 1)).next_in_segment 1 := by
  intro n hn hd
  simp [LubyState.next_in_segment]
  simp [add_assoc]
  exact (Nat.sub_eq_iff_eq_add hd).mp rfl

theorem LubyState.next_in_segment_increments_locIx (s : LubyState) (d : ℕ) (h : s.locIx + d < s.segment_height) :
    (s.next_in_segment d).locIx = s.locIx + d := by
  induction d with
  | zero => simp [LubyState.next_in_segment]
  | succ d hd =>
    have h' : s.locIx + d < s.segment_height := by exact Nat.lt_of_succ_lt h
    have t1 : s.next_in_segment (d + 1) = (s.next_in_segment d).next_in_segment 1 := by exact rfl
    simp [t1]
    nth_rw 1 [LubyState.next_in_segment]
    simp [hd h']
    exact rfl

theorem LubyState.next_in_segment_is_next (s : LubyState) (d : ℕ) (h : s.locIx + d < s.segment_height) :
    LubyState.next_in_segment s d = s.next d := by
  induction d with
  | zero => simp [LubyState.next_in_segment, LubyState.next]
  | succ d hd =>
    have t1 : s.next (d + 1) = (s.next d).next 1 := by exact rfl
    simp [t1]
    have h' : s.locIx + d < s.segment_height := by exact Nat.lt_of_succ_lt h
    have t2 : s.next_in_segment (d + 1) = (s.next_in_segment d).next_in_segment 1 := by exact rfl
    simp [t2]
    nth_rw 1 [LubyState.next_in_segment]
    simp [hd h']
    nth_rw 1 [LubyState.next]
    have t3 : (s.next d).next 0 = s.next d := by exact rfl
    simp [t3]
    simp [←hd h']
    simp [LubyState.is_segment_end]
    have t1 : (s.next_in_segment d).locIx = s.locIx + d := by exact rfl
    simp [t1]
    exact Nat.ne_of_lt h

theorem LubyState.segment_beg_transition' : ∀ n : ℕ, (LubyState.ofNat n).is_segment_beg = true →
    (LubyState.ofNat (n + (LubyState.ofNat n).segment_height)).is_segment_beg := by
  intro n hz
  let n' := LubyState.ofNat n
  have nn : n' = value_of% n' := by exact rfl
  simp [←nn]
  have z : n'.locIx = 0 := by simp [LubyState.is_segment_beg, ←nn] at hz ; exact hz
  have t1 : n + n'.segment_height = (n + n'.segment_height - 1) + 1 := by exact rfl
  rw [t1]
  have t2 : ofNat (n + n'.segment_height - 1 + 1) = (ofNat (n + n'.segment_height - 1)).next 1 := by
    exact rfl
  simp [t2]
  have t3 : n + n'.segment_height - 1 = n + (n'.segment_height - 1) := by exact rfl
  simp [t3]
  have t4 : ofNat (n + (n'.segment_height - 1)) = (ofNat n).next (n'.segment_height - 1) := by
    exact ofNat_dist n (n'.segment_height - 1)
  simp [t4]
  have t4 :
      (ofNat n).next (n'.segment_height - 1) = (ofNat n).next_in_segment (n'.segment_height - 1) := by
    refine Eq.symm (next_in_segment_is_next (ofNat n) (n'.segment_height - 1) ?_)
    simp [←nn, z]
    simp [LubyState.segment_height]
  simp [t4]
  simp [←nn]
  have t5 : (n'.next_in_segment (n'.segment_height - 1)).locIx = n'.locIx + n'.segment_height - 1 := by
    exact rfl
  rw [LubyState.next]
  simp [z] at t5
  split
  · expose_names ; simp [LubyState.is_segment_beg]
  · expose_names
    simp [LubyState.is_segment_end] at h
    rw [LubyState.next, t5] at h
    have t6 : (n'.next_in_segment (n'.segment_height - 1)).segment_height = n'.segment_height := by
      exact rfl
    simp [t6] at h
    have t7 : n'.segment_height - 1 + 1 = n'.segment_height := by exact t6
    exact absurd t7 h

def LubyState.segment_height_sum (b : ℕ) : ℕ := ∑ i ∈ Finset.range b, (trailing_zeros (i + 1) + 1)

-- #eval List.range 12 |>.map (fun n ↦ (LubyState.segment_height_sum n, LubyState.segment_height_sum' n))
#eval List.range 7 |>.map (fun k ↦ (2 ^ k, LubyState.segment_height_sum (2 ^ k), 2 ^ (k + 1) - 1))

#eval List.range 30 |>.map (fun n ↦ (
    (LubyState.ofNat (∑ k < (LubyState.ofNat n).segIx, (trailing_zeros k + 1) - 1)).segIx,
    (LubyState.ofNat n).segIx))

#eval List.range 20 |>.map (· + 1) |>.map (fun n ↦ (
  (∑ i ∈ Finset.range       n, (trailing_zeros       i + 1)),
  (∑ i ∈ Finset.range (n - 1), (trailing_zeros (i + 1) + 1) + 1)))

#eval List.range 7 |>.map (fun k ↦
  let n := 2 ^ k
  (∑ i ∈ Finset.range n, (trailing_zeros (i + 1) + 1), 2 ^ n.size - 1))

theorem LubyState.segment_height_sum_pow2 : ∀ n > 0, n = 2 ^ (n.size - 1) →
    ∑ i ∈ Finset.range n, (trailing_zeros (i + 1) + 1) = 2 ^ n.size - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro h
    have cases : n = 1 ∨ 1 < n := by exact LE.le.eq_or_lt' h
    rcases cases with case1|case2
    · simp [case1] at * ; simp [trailing_zeros]
    · intro h2
      have nsize2 : 2 ≤ n.size := by
        have u1 : (2 : ℕ).size ≤ n.size := by exact Nat.size_le_size case2
        have u2 : (2 : ℕ).size = 2 := by simp [Nat.size, Nat.binaryRec]
        simp [u2] at u1
        exact u1
      have t1 : Finset.range n = Finset.range (2 ^ (n.size - 1)) := by exact congrArg range h2
      simp [t1]
      have t2 : 2 ^ (n.size - 1) = 2 * 2 ^ (n.size - 1 - 1) := by
        refine Eq.symm (mul_pow_sub_one ?_ 2)
        · exact Nat.sub_ne_zero_of_lt (Nat.lt_size.mpr case2)
      simp [t2]
      clear t1 t2
      rw [two_mul]
      rw [Finset.sum_range_add]
      have sub1 : 2 ^ (n.size - 1 - 1) < n := by
        have t1 : 2 ^ n.size ≤ 2 * n := by exact pow2size_has_upper_bound n (by grind)
        have t2 : 2 ^ n.size / 2 ≤ 2 * n / 2 := by exact Nat.div_le_div_right t1
        have t3 : 2 * n / 2 = n := by grind
        simp [t3] at t2
        clear t3
        have t4 : 2 ^ n.size / 2 = 2 ^ (n.size - 1) := by
          refine Nat.div_eq_of_eq_mul_right (by grind) ?_
          · have : 2 = 2 ^ 1 := by exact rfl
            nth_rw 2 [this]
            exact Eq.symm (mul_pow_sub_one (by grind) (2 ^ 1))
        simp [t4] at t2
        have t5 : 2 ^ (n.size - 1 - 1) < 2 ^ (n.size - 1) := by
          refine Nat.two_pow_pred_lt_two_pow ?_
          refine Nat.zero_lt_sub_of_lt ?_
          exact Nat.lt_size.mpr case2
        exact Nat.lt_of_lt_of_le t5 t2
      have sub2 : 2 ^ (n.size - 1 - 1) > 0 := by
        exact Nat.two_pow_pos (n.size - 1 - 1)
      have sub3 : 2 ^ (n.size - 1 - 1) = 2 ^ ((2 ^ (n.size - 1 - 1)).size - 1) := by
        have : n.size - 1 - 1 = (2 ^ (n.size - 1 - 1)).size - 1 := by
          have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 - 1 + 1 := by exact Nat.size_pow
          simp [this]
        nth_rw 1 [this]
      have ih' := ih (2 ^ (n.size - 1 - 1)) sub1 sub2 sub3
      clear sub1 sub2 sub3
      simp [ih']
      have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 := by
        have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 - 1 + 1 := by exact Nat.size_pow
        simp [this]
        exact Nat.sub_add_cancel (Nat.le_sub_one_of_lt nsize2)
      simp [this]
      clear this
      -- 最後の1個を一旦外す
      have t1 : 2 ^ (n.size - 1 - 1) = 2 ^ (n.size - 1 - 1) - 1 + 1 := by
        exact Eq.symm (Nat.sub_add_cancel Nat.one_le_two_pow)
      nth_rw 1 [t1]
      rw [Finset.sum_range_succ]
      -- shift left part1
      have t2 : ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1), (trailing_zeros (2 ^ (n.size - 1 - 1) + x + 1) + 1) =
          ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1), (trailing_zeros (x + 1) + 1) := by
        refine trailing_zeros_prop8 (n.size - 1 - 1) (2 ^ (n.size - 1 - 1)) ?_
        exact Nat.le_refl (2 ^ (n.size - 1 - 1))
      simp [t2]
      clear t2
      have t3 : 2 ^ (n.size - 1 - 1) + (2 ^ (n.size - 1 - 1) - 1) + 1 = 2 ^ (n.size - 1) := by
        have : 2 ^ (n.size - 1 - 1) + (2 ^ (n.size - 1 - 1) - 1) + 1 =
            2 ^ (n.size - 1 - 1) + 2 ^ (n.size - 1 - 1) - 1 + 1 := by
          refine Nat.add_right_cancel_iff.mpr ?_
          · exact Eq.symm (Nat.add_sub_assoc Nat.one_le_two_pow (2 ^ (n.size - 1 - 1)))
        simp [this]
        refine Eq.symm (Nat.eq_add_of_sub_eq ?_ ?_)
        · exact Nat.one_le_two_pow
        · have : 2 ^ (n.size - 1) = 2 ^ (n.size - 1 - 1) + 2 ^ (n.size - 1 - 1) := by
            have : 2 ^ (n.size - 1 - 1) + 2 ^ (n.size - 1 - 1) = 2 ^ (n.size - 1 - 1 + 1) := by
              exact Eq.symm (Nat.two_pow_succ (n.size - 1 - 1))
            simp [this]
            exact (Nat.sub_eq_iff_eq_add nsize2).mp rfl
          simp [this]
      simp [t3]
      -- shift left part 2
      have t4 : trailing_zeros (2 ^ (n.size - 1)) = trailing_zeros (2 ^ (n.size - 1 - 1)) + 1 := by
        have s1 : trailing_zeros (2 ^ (n.size - 1)) = n.size - 1 := by
          exact trailing_zeros_prop3 (n.size - 1)
        have s2 : trailing_zeros (2 ^ (n.size - 1 - 1)) = n.size - 1 - 1 := by
          exact trailing_zeros_prop3 (n.size - 1 - 1)
        simp [s1, s2]
        grind
      simp [t4]
      have t5 :
          ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1),
            (trailing_zeros (x + 1) + 1) + (trailing_zeros (2 ^ (n.size - 1 - 1)) + 1 + 1) =
          ∑ x ∈ range (2 ^ (n.size - 1 - 1) - 1),
            (trailing_zeros (x + 1) + 1) + (trailing_zeros (2 ^ (n.size - 1 - 1)) + 1) + 1 := by
        exact rfl
      simp only [t5]
      have t6 : (2 ^ (n.size - 1 - 1) - 1 + 1) = (2 ^ (n.size - 1 - 1)) := by grind
      nth_rw 2 [←t6]
      clear t5 t4 t3 t1
      rw [←Finset.sum_range_succ (fun n ↦ trailing_zeros (n + 1) + 1) (2 ^ (n.size - 1 - 1) - 1)]
      simp [t6, ih']
      have t8 : (2 ^ (n.size - 1 - 1)).size = n.size - 1 := by
        have : (2 ^ (n.size - 1 - 1)).size = n.size - 1 - 1 + 1 := by exact Nat.size_pow
        simp [this]
        grind
      simp [t8]
      have t9 : 2 ^ (n.size - 1) - 1 + 1 = 2 ^ (n.size - 1) := by grind
      simp [t9]
      have t10: 2 ^ (n.size - 1) - 1 + 2 ^ (n.size - 1) = 2 ^ (n.size - 1) + 2 ^ (n.size - 1) - 1 := by
        exact Eq.symm (Nat.sub_add_comm Nat.one_le_two_pow)
      simp [t10]
      have t11 : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) = 2 ^ n.size := by
        have : 2 ^ (n.size - 1) + 2 ^ (n.size - 1) = 2 * 2 ^ (n.size - 1) := by
          exact Eq.symm (Nat.two_mul (2 ^ (n.size - 1)))
        simp [this]
        have : 2 * 2 ^ (n.size - 1) = 2 ^ (n.size - 1 + 1) := by exact Eq.symm Nat.pow_succ'
        simp [this]
        exact Nat.sub_add_cancel (Nat.one_le_of_lt nsize2)
      simp [t11]

#eval List.range 7 |>.map (2 ^ · - 1) |>.map (fun n ↦ (n, (LubyState.ofNat (n - 1)).segIx, 2 ^ (n.size - 1)))

-- これはenvelopeはいくつのsegmentを必要とするかという問題。
-- ∑ i ∈ range (2 ^ (k.size - 1)), trailing_zeros · = k から
-- n = 2 ^ n.size - 1 の大きさのenvelopには2 ^ (n.size - 1) segmentsが必要であるため、
-- 次のn + 1に対しては当然2 ^ n.size segmentsが必要。
theorem t20250910 : ∀ n : ℕ, n = 2 ^ (n.size - 1) - 1 → (LubyState.ofNat (n - 1)).segIx = n + 1 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have zp : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
    rcases zp with z|p
    · simp [z] at *
      simp [LubyState.ofNat, LubyState.zero, LubyState.next]
      exact rfl
    · sorry

theorem t20250904 : ∀ n : ℕ,
    (LubyState.ofNat (∑ k < (LubyState.ofNat n).segIx, (trailing_zeros k + 1) - 1)).segIx
    = (LubyState.ofNat n).segIx := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have p2_not : n = 2 ^ (n.size - 1) ∨ ¬n = 2 ^ (n.size - 1) := by
      exact eq_or_ne n (2 ^ (n.size - 1))
    rcases p2_not with p2|not
    · sorry
    · sorry

-- 筋が悪い。s.segIx = k に対して (ofNat (∑ k, trailing_zeros k)).segId = s.segIx 的な方向であるべき
-- あるいは segment_beg な (ofNat n).segIx = k に対して (ofNat (∑ k, trailing_zeros k)).segId = n 的な
-- ことからsegIxを剥ぎ取ってnに持ち込める。
theorem LubyState.segment_height_sum_is_envelope : ∀ k : ℕ,
    LubyState.segment_height_sum (2 ^ k) = 2 ^ (k + 1) - 1 := by
  intro k
  simp [segment_height_sum]
  induction k with
  | zero => simp [trailing_zeros]
  | succ k ih =>
    have t1 : ∑ i ∈ range (2 ^ (k + 1) - 2 + 2), (trailing_zeros (i + 1) + 1) =
      ∑ i ∈ range (2 ^ (k + 1) - 2), (trailing_zeros (i + 1) + 1)
      + ∑ i ∈ range 2, (trailing_zeros (2 ^ (k + 1) - 2 + i + 1) + 1) := by
      exact sum_range_add (fun x ↦ trailing_zeros (x + 1) + 1) (2 ^ (k + 1) - 2) 2
    have t2 : 2 ^ (k + 1) - 2 + 2 = 2 ^ (k + 1) := by
      exact Nat.sub_add_cancel (Nat.le_self_pow (Ne.symm (Nat.zero_ne_add_one k)) 2)
    simp [t2] at t1
    simp [t1]
    have t3 : ∑ i ∈ range 2, (trailing_zeros (2 ^ (k + 1) - 2 + i + 1) + 1) =
        (trailing_zeros (2 ^ (k + 1) - 2 + 0 + 1) + 1) + (trailing_zeros (2 ^ (k + 1) - 2 + 1 + 1) + 1)
        := by
      exact rfl
    simp [t3]
    have t4 : 2 ^ (k + 1) - 2 + 1 = 2 ^ (k + 1) - 1 := by
      exact Eq.symm ((fun {n m} ↦ Nat.pred_eq_succ_iff.mpr) (id (Eq.symm t2)))
    simp [t4]
    have t5 : 2 ^ (k + 1) - 1 + 1 = 2 ^ (k + 1) := by exact Nat.sub_add_cancel Nat.one_le_two_pow
    simp [t5]
    have t6 : trailing_zeros (2 ^ (k + 1)) = k + 1 := by exact trailing_zeros_prop3 (k + 1)
    simp [t6]
    have t7 : trailing_zeros (2 ^ (k + 1) - 1) = 0 := by exact trailing_zeros_prop4 (k + 1)
    simp [t7]
    have zp : k = 0 ∨ k > 0 := by exact Nat.eq_zero_or_pos k
    rcases zp with z|p
    · simp [z] at *
    · have : range (2 ^ (k + 1) - 2) = range (2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2)) := by
        have t1 : 2 ^ (k + 1) = 2 ^ k + (2 ^ (k + 1) - 2 ^ k) := by grind
        have t2 : 2 ^ (k + 1) - 2 = 2 ^ k + (2 ^ (k + 1) - 2 ^ k) - 2 := by grind
        have t2' : 2 ^ (k + 1) - 2 = 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) := by
          refine Nat.sub_eq_of_eq_add ?_
          have : 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) + 2 = 2 ^ k + 2 ^ (k + 1) - 2 ^ k - 2 + 2 := by
            have : 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) = 2 ^ k + 2 ^ (k + 1) - 2 ^ k - 2 := by
              have : 2 ^ k + (2 ^ (k + 1) - 2 ^ k - 2) = 2 ^ k + 2 ^ (k + 1) - 2 ^ k - 2 := by
                have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by exact Nat.two_pow_succ k
                simp [this]
                have : 2 ^ k + (2 ^ k - 2) = 2 ^ k + 2 ^ k - 2 := by
                  exact Eq.symm (Nat.add_sub_assoc (Nat.le_pow p) (2 ^ k))
                simp [this]
              simp [this]
            exact Nat.add_left_inj.mpr this
          simp [this]
          grind
        rw [←t2']
      simp [this]
      simp [Finset.sum_range_add]
      simp [ih]
      have t8 : 2 ^ (k + 1) - 2 ^ k = 2 ^ k := by
        refine Nat.sub_eq_of_eq_add ?_
        · rw [←mul_two]
          exact rfl
      simp [t8]
      have t9 : ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (2 ^ k + i + 1) + 1)
          = ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (      i + 1) + 1) := by
        exact trailing_zeros_prop8 k (2 ^ k - 1) (Nat.sub_le (2 ^ k) 1)
      simp [t9]
      have t10 : ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (i + 1) + 1) + (trailing_zeros (2 ^ k - 2 + 1) + 1) := by
        have s1 : 2 ^ k - 1 = 2 ^ k - 1 - 1 + 1 := by
          refine Eq.symm (Nat.sub_add_cancel ?_)
          · exact Nat.le_sub_one_of_lt (Nat.one_lt_two_pow (Nat.ne_zero_of_lt p))
        nth_rw 1 [s1]
        have s2 : 2 ^ k - 1 - 1 = 2 ^ k - 2 := by exact rfl
        nth_rw 1 [s2]
        rw [sum_range_succ]
      have t10' : ∑ i ∈ range (2 ^ k - 2), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) - (trailing_zeros (2 ^ k - 2 + 1) + 1) := by
        exact Nat.eq_sub_of_add_eq (id (Eq.symm t10))
      simp [t10']
      clear t10' t10 t9 t8 t7 t6 t5 t4 t3 t2 t1 this
      have t1 : trailing_zeros (2 ^ k - 2 + 1) + 1 = 1 := by
        have : 2 ^ k - 2 + 1 = 2 ^ k - 1 := by
          have s1 : 2 ^ k - 2 + 2 = 2 ^ k := by exact Nat.sub_add_cancel (Nat.le_pow p)
          have s2 : 2 = 1 + 1 := by exact rfl
          nth_rw 3 [s2] at s1
          have s3 : 2 ^ k - 2 + (1 + 1) = 2 ^ k - 2 + 1 + 1 := by exact rfl
          simp [s3] at s1
          exact Eq.symm ((fun {n m} ↦ Nat.pred_eq_succ_iff.mpr) (id (Eq.symm s1)))
        simp [this]
        exact trailing_zeros_prop4 k
      simp [t1]
      have t2 : ∑ i ∈ range (2 ^ k), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) + (trailing_zeros (2 ^ k - 1 + 1) + 1) := by
        have s1 : 2 ^ k = 2 ^ k - 1 + 1 := by
          exact Eq.symm (Nat.sub_add_cancel Nat.one_le_two_pow)
        nth_rw 1 [s1]
        rw [sum_range_succ]
      have t2' : ∑ i ∈ range (2 ^ k - 1), (trailing_zeros (i + 1) + 1) =
          ∑ i ∈ range (2 ^ k), (trailing_zeros (i + 1) + 1) - (trailing_zeros (2 ^ k - 1 + 1) + 1) := by
        exact Nat.eq_sub_of_add_eq (id (Eq.symm t2))
      simp [t2', ih]
      have t3 : trailing_zeros (2 ^ k - 1 + 1) = k := by
        have : 2 ^ k - 1 + 1 = 2 ^ k := by exact Nat.sub_add_cancel Nat.one_le_two_pow
        simp [this]
        exact trailing_zeros_prop3 k
      simp [t3]
      rw [add_comm]
      have t4 : 2 ^ (k + 1) - 1 + (2 ^ (k + 1) - 1 - (k + 1) - 1)
          = 2 ^ (k + 1) + (2 ^ (k + 1) - 1 - (k + 1) - 1) - 1 := by
        exact Eq.symm (Nat.sub_add_comm (by grind))
      simp [t4]
      let x := 1 + (k + 1) + 1
      have hx : x = value_of% x := by exact rfl
      have base1 : (k + 1) + 2 ≤ 2 ^ (k + 1) := by
        let x := k - 1
        have hx : x = value_of% x := by exact rfl
        have hx' : x + 1 = k := by exact Nat.sub_add_cancel p
        simp [←hx']
        induction x with
        | zero => simp
        | succ x hx =>
          have s1 : x + 1 + 1 + 1 + 2 = 1 + (x + 1 + 1 + 2) := by grind
          simp [s1]
          have s2 : 1 < 2 ^ (x + 1 + 1) := by exact Nat.lt_of_add_left_lt hx
          have s3 : 2 ^ (x + 1 + 1 + 1) = 2 ^ (x + 1 + 1) + 2 ^ (x + 1 + 1) := by
            exact Nat.two_pow_succ (x + 2)
          simp [s3]
          exact Nat.add_le_add Nat.one_le_two_pow hx
      have t5 : 2 ^ (k + 1) - 1 - (k + 1) - 1 = 2 ^ (k + 1) - x := by
        simp [hx]
        refine (Nat.sub_eq_iff_eq_add ?_).mpr ?_
        · refine Nat.le_sub_of_add_le ?_
          · refine Nat.add_le_of_le_sub ?_ ?_
            · exact Nat.le_sub_one_of_lt Nat.lt_two_pow_self
            · exact Nat.le_sub_of_add_le (Nat.one_add_le_iff.mpr (Nat.lt_sub_of_add_lt base1))
        · have : 2 ^ (k + 1) - (1 + (k + 1) + 1) + 1 = 2 ^ (k + 1) - (k + 1) - 1 := by
            have : 2 ^ (k + 1) - (1 + (k + 1) + 1) + 1 = 2 ^ (k + 1) + 1 - (1 + (k + 1) + 1) := by
              refine Eq.symm (Nat.sub_add_comm ?_)
              refine Nat.add_le_of_le_sub ?_ ?_
              · exact Nat.one_le_two_pow
              · have s1 : (k + 1) + 1 + 1 ≤ 2 ^ (k + 1) := by exact base1
                have s2 : 1 + (k + 1) + 1 = k + 1 + 1 + 1 := by exact Eq.symm (Nat.add_comm (k + 1 + 1) 1)
                simp [←s2] at s1
                exact Nat.le_sub_one_of_lt s1
            simp [this]
            exact Nat.Simproc.sub_add_eq_comm (2 ^ (k + 1)) 1 (k + 1)
          simp [this]
          exact Nat.sub_right_comm (2 ^ (k + 1)) 1 (k + 1)
      simp [t5]
      have t6 : 2 ^ (k + 1) + (2 ^ (k + 1) - x) = 2 ^ (k + 1) + 2 ^ (k + 1) - x := by
        refine Eq.symm (Nat.add_sub_assoc ?_ (2 ^ (k + 1)))
        · simp [hx] ; rw [add_comm, ←add_assoc] ; simp [add_comm] ; exact base1
      simp [t6]
      have t7 : 2 ^ (k + 1) + 2 ^ (k + 1) = 2 ^ (k + 1 + 1) := by exact Eq.symm (Nat.two_pow_succ (k + 1))
      simp [t7, hx]
      have t8 : 1 + (k + 1 + 1) = k + 1 + 1 + 1 := by exact Nat.add_comm 1 (k + 1 + 1)
      simp [t8]
      let y := k + 1 + 1 + 1
      have hy : y = value_of% y := by exact rfl
      have t9 : 1 + (k + 1) + 1 = y := by grind
      simp [t9 , ←hy]
      have t10 : 2 ^ (k + 1 + 1) - y - 1 = 2 ^ (k + 1 + 1) - (y + 1) := by exact rfl
      simp [t10]
      simp [hy]
      clear t10 t9 t8 t7 t6 t5 t4 t3 t2' t2 t1 hy x y hx
      rw [add_comm]
      have cond {k : ℕ} (h : 0 < k) : 2 ^ (k + 1 + 1) ≥ (k + 1 + 1 + 1 + 1) := by
        induction k with
        | zero => simp
        | succ k ih =>
          expose_names
          clear ih_1
          have two_cases : k = 0 ∨ ¬k = 0 := by exact Or.symm (ne_or_eq k 0)
          rcases two_cases with k0|kp
          · simp [k0]
          · have kp' : 0 < k := by exact Nat.zero_lt_of_ne_zero kp
            have t1 : 2 ^ (k + 1 + 1 + 1) = 2 * 2 ^ (k + 1 + 1) := by exact Nat.pow_succ'
            rw [mul_comm, mul_two] at t1
            simp [t1]
            exact Nat.add_le_add (ih kp') Nat.one_le_two_pow
      have : 2 ^ (k + 1 + 1) - (k + 1 + 1 + 1 + 1) + (k + 1 + 1 + 1)
          = 2 ^ (k + 1 + 1) + (k + 1 + 1 + 1) - (k + 1 + 1 + 1 + 1) := by
        exact Eq.symm (Nat.sub_add_comm (cond p))
      simp [this]
      grind

-- これはsegment単位でしか説明できない
theorem LubyState.segment_height_prop1 : ∀ n > 0, n ≠ 2 ^ (n.size - 1) →
    (LubyState.ofNat n).segment_height = (LubyState.ofNat (n - 2 ^ (n.size - 1))).segment_height := by
  intro n hn1 hn2
  simp [LubyState.segment_height]
  have : trailing_zeros (ofNat n).segIx = trailing_zeros (ofNat (n - 2 ^ (n.size - 1))).segIx := by
    sorry -- apply?
  sorry
  --

theorem LubyState.segment_beg_prop1 : ∀ n > 0, n ≠ 2 ^ (n.size - 1) →
    (LubyState.ofNat n).is_segment_beg = (LubyState.ofNat (n - 2 ^ (n.size - 1))).is_segment_beg := by
  simp [LubyState.is_segment_beg, LubyState.ofNat]
  sorry -- FIXME: todo

theorem LubyState.define_recursively2 : ∀ n : ℕ,
    LubyState.zero.next n = LubyState.mk (LubyState.toSegIx n 0 0) (LubyState.toLocIx n) := by
  sorry
