import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Utils

namespace Tree

/-
 - The level of LubyTrees starts with 1.
 - The index of the elements of LubyTree starts with 0.
 -/

inductive LubyTree where
  | leaf : LubyTree
  | wrap (tree : LubyTree) : LubyTree
deriving BEq

def LubyTree.mk (level : Nat) : LubyTree := match level with
  | 0     => LubyTree.leaf
  | l + 1 => wrap (LubyTree.mk l)

def LubyTree.toString (self : LubyTree) : String := match self with
  | .leaf => "leaf"
  | wrap (tree : LubyTree) => s!"↑{tree.toString}"

instance : ToString LubyTree where
  toString := LubyTree.toString

def t4 := LubyTree.mk 4
#eval t4 -- LubyTree.mk 4

def LubyTree.depth (self : LubyTree) : Nat := match self with
  | .leaf => 1
  | wrap tree => tree.depth + 1

theorem LubyTree.depth_gt_one : ∀ t : LubyTree, t.depth ≥ 1 := by
  intro t
  induction t <;> simp [LubyTree.depth]

theorem LubyTree.mk_of_depth_eq_self (t : LubyTree) : LubyTree.mk (t.depth - 1) = t := by
  induction t with
  | leaf => simp [LubyTree.depth, LubyTree.mk]
  | wrap sub =>
    expose_names
    simp [LubyTree.depth]
    rw [LubyTree.mk.eq_def]
    split
    {
      expose_names
      have this := LubyTree.depth_gt_one sub
      have : ¬sub.depth = 0 := by exact Nat.ne_zero_of_lt this
      exact absurd heq this
    }
    {
      expose_names
      have : sub.depth - 1 = l.succ - 1 := by exact congrFun (congrArg HSub.hSub heq) 1
      have : sub.depth - 1 = l := by exact this
      simp [←this, tree_ih]
    }

theorem LubyTree.wrap_n_eq_n_add_one (n : Nat) : LubyTree.wrap (LubyTree.mk n) = LubyTree.mk (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [←ih]
    nth_rw 2 [LubyTree.mk.eq_def]
    split
    {
      expose_names
      have (n : Nat) : n + 1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one n)
      have hne := this (n + 1)
      exact absurd heq hne
    }
    {
      expose_names
      have : n + 1 = l := by exact Nat.succ_inj.mp heq
      rw [←this]
      simp [ih]
    }

def LubyTree.size (self : LubyTree) : Nat := match self with
  | .leaf => 1
  | wrap tree => tree.size * 2 + 1

#eval List.range 5 |>.map (fun n ↦ (LubyTree.mk n).size)

theorem LubyTree.size_ge_one (t : LubyTree) : t.size ≥ 1 := by
  induction t <;> simp [LubyTree.size]

theorem size_is_two_sub_sizes_add_one (n : Nat) :
    (LubyTree.mk (n + 1)).size = 2 * (LubyTree.mk n).size + 1 := by
  rw [LubyTree.mk, LubyTree.size]
  grind
 
theorem size_is_two_sub_sizes_add_one' (n : Nat) :
    (LubyTree.mk n).wrap.size = 2 * (LubyTree.mk n).size + 1 := by
  simp [←size_is_two_sub_sizes_add_one]
  exact rfl

#eval Nat.bits (2 * 5)

theorem length_of_bits_eq_size (n : Nat) : n.bits.length = n.size := by exact Nat.size_eq_bits_len n

theorem bits_of_double_eq_cons_false_and_bits (n : Nat) (h : n > 0) :
    (2 * n).bits = false :: n.bits := by
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt h
  exact Nat.bit0_bits n this

example (n : Nat) : (2 * n + 1).bits = true :: n.bits := by
  exact Nat.bit1_bits n

theorem size_of_two_mul_eq_aize_add_one (n : Nat) (h : n > 0) : n.size + 1 = (n * 2).size := by
  simp [←Nat.size_eq_bits_len, Nat.mul_comm n 2, bits_of_double_eq_cons_false_and_bits n h]

theorem depth_and_size (tree : LubyTree) : tree.depth = tree.size.size := by
  induction tree
  { simp [LubyTree.depth, LubyTree.size] }
  {
    expose_names
    simp [LubyTree.depth]
    simp [LubyTree.size]
    simp [tree_ih]
    simp [←length_of_bits_eq_size, Nat.mul_comm tree.size 2]
  }

def LubyTree.enveloveMax (t : LubyTree) : Nat := 2 ^ (t.depth - 1) - 1

/- This is an envelove that covers the last segment. -/ 
def LubyTree.valueAtSize (self : LubyTree) (s : Nat) : Nat := match self with
  | .leaf     => 1
  | .wrap sub =>
    if self.size ≤ s then 2 ^ self.depth.pred else sub.valueAtSize ((s - 1) % sub.size + 1)

def LubyTree.valueAt (s : Nat) : Nat := (LubyTree.mk (2 ^ s.size.succ)).valueAtSize s

#eval List.range 28 |>.map (fun n ↦ LubyTree.valueAt n.succ)

theorem LubyTree.bit_patterns_of_top (t : LubyTree) : t.size.bits.all (· = true) := by
  induction t
  { simp [LubyTree.size] }
  {
    expose_names
    let n := tree.depth
    have hn : n = value_of% n := by rfl
    have : LubyTree.mk (n - 1) = tree := by simp [hn] ; exact LubyTree.mk_of_depth_eq_self tree
    simp -- [LubyTree.size]
    simp at tree_ih
    simp only [←this, size_is_two_sub_sizes_add_one' (n - 1)]
    simp only [Nat.bit1_bits]
    have notin_cons (a : Bool) (l : List Bool) : false ≠ a → false ∉ l → false ∉ a :: l := by 
      exact fun a_1 a_2 ↦ List.not_mem_cons_of_ne_of_not_mem a_1 a_2
    apply notin_cons
    { simp }
    { simp [this] ; exact tree_ih }
  }

theorem LubyTree.is_symmetry (d : Nat) :
    ∀ n ≤ ((LubyTree.mk d).size - 1) / 2,
      (LubyTree.mk d).valueAtSize n = (LubyTree.mk d).valueAtSize (n + ((LubyTree.mk d).size - 1) / 2)  := by
  intro n hn
  induction' d with d dh
  { 
    simp [LubyTree.mk]
    simp [LubyTree.size]
  }
  {
    rw [LubyTree.valueAtSize.eq_def]
    rw [LubyTree.valueAtSize.eq_def]
    split
    { rfl } -- case: leaf
    {
      -- case: wrap sub
      expose_names
      have d_tree : mk d = tree := by sorry

      have : (n - 1) % tree.size + 1 = (n + ((mk (d + 1)).size - 1) / 2 - 1) % tree.size + 1 := by sorry
      simp only [←this]
      -- swap left and right to split by more complex term
      split
      {
        -- case: top or over
        expose_names
        rw [LubyTree.valueAtSize.eq_def]
        split
        { exact rfl }
        {
          expose_names
          simp [←d_tree] at *

          sorry }
      }
      {
        split
        {sorry}
        {
          -- case: go down recursively
          exact rfl 
        }
      }
   }
 }

end Tree

