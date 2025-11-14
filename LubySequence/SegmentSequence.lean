import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Finset.Basic
import LubySequence.Basic
import LubySequence.Segment
import LubySequence.TrailingZeros
import LubySequence.Utils

structure Segment where
  start : ℕ
  index : ℕ

def Segment.default : Segment := ⟨1, 1⟩

instance Segment.inst : Inhabited Segment := ⟨1, 1⟩
instance Segment.repl : Repr Segment where
  reprPrec s _ := "Seg{" ++ toString s.start ++ ":" ++ toString s.index ++ "}"

#eval Segment.default

def Segment.length (s : Segment) : ℕ := trailing_zeros s.index + 1
def Segment.sum (s : Segment) : ℕ := s.start + s.length

/--
Direct conversion version
-/
@[simp]
def Segment.next (self : Segment) (repeating : ℕ := 1) : Segment :=
  match repeating with
  | 0     => self
  | r + 1 => (Segment.mk self.sum (self.index + 1)).next r

#eval List.range 10 |>.map (fun n ↦ Segment.default.next n)

def Segment.nextTo (s : Segment) (n : ℕ) : Segment := if s.sum ≥ n then s else (s.next).nextTo n
termination_by (n - s.sum)
decreasing_by
  expose_names
  simp at h
  simp [Segment.next]
  rw (occs := .pos [1]) [Segment.sum]
  simp [Segment.length]
  refine Nat.sub_lt_sub_left ?_ ?_
  · exact h
  · exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ (trailing_zeros (s.index + 1)))

/-
theorem build_state_is_additive (a b : ℕ) :
    build_state (a + b) 0 1 = build_state (a + b) (build_state a 0 1).fst (build_state a 0 1).snd := by
  sorry
  -/

/-
partial
def state_from' (n n' si : ℕ) : ℕ × ℕ :=
  let z := trailing_zeros si + 1
  if n' + z > n then (si, n - n') else state_from' n (n' + z) (si + 1)

def state_from (n : ℕ) : ℕ × ℕ := state_from' n 0 1

#eval List.range 14 |>.map (LubyState.zero.next ·)
#eval List.range 14 |>.map state_from

theorem t2025114 : ∀ n : ℕ, (state_from (∑ i ∈ range n, (trailing_zeros i + 1))).snd = 0 := by
  intro n
  induction n with
  | zero => simp [state_from, state_from']
  | succ n ih =>
    simp [state_from]
    rw [state_from']
    split <;> expose_names
    · simp at h
      simp
      exact h
    · have : state_from
      sorry
-/
