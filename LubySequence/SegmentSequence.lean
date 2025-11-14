import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Mathlib.Data.Finset.Basic
import LubySequence.Basic
import LubySequence.Segment
import LubySequence.State
import LubySequence.TrailingZeros
import LubySequence.Utils

/-!
Direct conversion version of segment manipulation
-/

open Finset

structure Segment where
  index : ℕ
  start : ℕ
  index_ge_1 : index ≥ 1 := by grind

def Segment.zero : Segment := ⟨1, 1, by grind⟩

instance Segment.inst : Inhabited Segment := ⟨1, 1, by grind⟩
instance Segment.repl : Repr Segment where
  reprPrec s n := "Seg" ++ reprPrec s.index n ++ ":" ++ reprPrec s.start n

def Segment.length (s : Segment) : ℕ := trailing_zeros s.index + 1
def Segment.sum (s : Segment) : ℕ := s.start + s.length

@[simp]
def Segment.next (self : Segment) (repeating : ℕ := 1) : Segment :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let s := self.next r
    Segment.mk (s.index + 1) s.sum (by exact Nat.le_add_left 1 s.index)

#eval List.range 10 |>.map (fun n ↦ Segment.zero.next n)

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

#eval List.range 14 |>.map (LubyState.zero.next ·)
#eval List.range 14 |>.map (Segment.zero.next ·)

theorem segment_is_additive (a b : ℕ) : Segment.zero.next (a + b) = (Segment.zero.next a).next b := by
  induction b with
  | zero => simp
  | succ b' ih => rw [←add_assoc] ; simp [Segment.next, ih]

theorem segment_sum_eq_segment_length_sum : ∀ n : ℕ,
    (Segment.zero.next (∑ i ∈ range n, (trailing_zeros i + 1))).sum =
    ∑ i ∈ range n, (trailing_zeros i + 1) :=
  sorry

/-
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
