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

namespace Segment

def zero : Segment := ⟨1, 0, by grind⟩

instance inst : Inhabited Segment where
  default := zero

instance repl : Repr Segment where
  reprPrec s n := "Seg" ++ reprPrec s.index n ++ ":" ++ reprPrec s.start n

def length (s : Segment) : ℕ := trailing_zeros s.index + 1
def sum (s : Segment) : ℕ := s.start + s.length

@[simp]
def next (self : Segment) (repeating : ℕ := 1) : Segment :=
  match repeating with
  | 0     => self
  | r + 1 =>
    let s := self.next r
    Segment.mk (s.index + 1) s.sum (by exact Nat.le_add_left 1 s.index)

#eval List.range 14 |>.map (LubyState.zero.next ·)
#eval List.range 14 |>.map (zero.next ·)
#eval List.range 10 |>.map (Segment.zero.next ·)
 
theorem segment_is_additive (a b : ℕ) : zero.next (a + b) = (zero.next a).next b := by
  induction b with
  | zero => simp
  | succ b' ih => simp at ih ; rw [←add_assoc] ; simp [next, ih]


#eval List.range 20 |>.map (fun n ↦ (n + 1, (Segment.zero.next n).index))

theorem segment_index_for_n : ∀ n : ℕ, (Segment.zero.next n).index = n + 1 := by
  intro n
  induction n with
  | zero => simp [zero]
  | succ n ih => rw [next] ; simp [ih]

theorem segment_length_for_n : ∀ n : ℕ, (Segment.zero.next n).length = trailing_zeros (n + 1) + 1 := by
  intro n
  simp [length]
  rw [segment_index_for_n n]

#eval List.range 20
    |>.map (fun n ↦ (n, (Segment.zero.next n).start, ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))

theorem segment_start_for_n : ∀ n : ℕ, (Segment.zero.next n).start = ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) := by
  intro n
  induction n with
  | zero => simp [range, zero]
  | succ n' ih =>
    simp only [next, sum, ih, length, segment_index_for_n]
    exact Eq.symm (sum_range_succ (fun x ↦ trailing_zeros (x + 1) + 1) n')

theorem segment_for_n :
    ∀ n > 0, ∑ i ∈ range n, (trailing_zeros i + 1) = (Segment.zero.next (n - 1)).start + 1 := by
  intro n n_gt_0
  rw [segment_start_for_n (n - 1)]
  have : 
      ∑ i ∈ range 1, (trailing_zeros i + 1) + ∑ i ∈ range (n - 1), (trailing_zeros (1 + i) + 1) =
      ∑ i ∈ range (1 + (n - 1)), (trailing_zeros i + 1) := by
    exact Eq.symm (sum_range_add (fun x ↦ trailing_zeros x + 1) 1 (n - 1))
  have aux : 
      ∑ i ∈ range (n - 1), (trailing_zeros (1 + i) + 1) =
      ∑ i ∈ range (n - 1), (trailing_zeros (i + 1) + 1) := by
    refine sum_equiv ?_ (fun i ↦ ?_) ?_
    · exact Denumerable.eqv ℕ
    · simp
      constructor <;> exact fun a ↦ a
    · intro n' n'_def
      refine Nat.add_left_inj.mpr ?_
      · have : 1 + n' = (Denumerable.eqv ℕ) n' + 1 := by exact Nat.add_comm 1 n'
        exact congrArg trailing_zeros this
  simp [aux] at this
  have aux : 1 + (n - 1) = n := by grind
  simp [aux] at this
  rw [add_comm] at this
  simp [this]

def within' (limit : ℕ) (n : ℕ) : Segment := match n with
  | 0 => Segment.zero
  | n' + 1 => if (Segment.zero.next n).start < limit then Segment.zero.next n else within' limit n'

@[simp]
def within (limit : ℕ) : Segment := within' limit limit

#eval List.range 20 |>.map (fun n ↦ Segment.zero.next n)
#eval List.range 20
    |>.map (fun n ↦ (n, ∑ i ∈ range n, (trailing_zeros i + 1)))
    |>.map (fun (n, m) ↦ (n, m, (Segment.zero.next (n - 1)).start + 1, (within m).start + 1))
#eval List.range 20
    |>.map (fun n ↦ (n, ∑ i ∈ range n, (trailing_zeros i + 1)))
    |>.map (fun (n, m) ↦ (n, m, Segment.zero.next (n - 1), within m))

theorem segment_for_within_n :
    ∀ n > 0, within (∑ i ∈ range n, (trailing_zeros i + 1)) = Segment.zero.next (n - 1) := by
  sorry


/- def nextTo' (s : Segment) (n : ℕ) : Segment := if s.sum ≥ n then s else (s.next).nextTo' n
termination_by (n - s.sum)
decreasing_by
  expose_names
  simp at h
  simp [next]
  rw (occs := .pos [1]) [sum]
  simp [length]
  refine Nat.sub_lt_sub_left ?_ ?_
  · exact h
  · exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ (trailing_zeros (s.index + 1))) -/

#eval List.range 20
    |>.map (fun n ↦ ((within (∑ i ∈ range n, (trailing_zeros (i + 1) + 1))).sum,
      ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)))

theorem segment_sum_eq_segment_length_sum : ∀ n > 0,
    (within (∑ i ∈ range n, (trailing_zeros (i + 1) + 1))).sum =
    ∑ i ∈ range n, (trailing_zeros (i + 1) + 1) := by
  intro n n_gt_0
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases n_eq_0 : n = 0
    · rw [n_eq_0]
      simp [range]
      simp [within', sum, length, zero]
    · rename' n_eq_0 => n_gt_0
      replace n_gt_0 : n > 0 := by exact Nat.zero_lt_of_ne_zero n_gt_0
      replace ih := ih n_gt_0
      let n' := ∑ i ∈ range 1, (trailing_zeros (n + i + 1) + 1)
      have n'_def : n' = value_of% n' := rfl
      simp at n'_def
      have n'_gt_0 : n' > 0 := by exact Nat.zero_lt_succ (trailing_zeros (n + 0 + 1))
      let sumₙ := ∑ i ∈ range n, (trailing_zeros (i + 1) + 1)
      have sumₙ_def : sumₙ = value_of% sumₙ := rfl
      have : ∑ i ∈ range (n + 1), (trailing_zeros (i + 1) + 1) = sumₙ + n' := by
        exact sum_range_add (fun x ↦ trailing_zeros (x + 1) + 1) n 1
      simp only [this]
      simp only [←sumₙ_def] at * -- ih
      have : (within sumₙ).index = n := by
        sorry
      -- rw [within'.eq_def]
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

end Segment
