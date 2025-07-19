import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

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

theorem size_is_two_sub_sizes_add_one (n : Nat) :
    (LubyTree.mk (n + 1)).size = 2 * (LubyTree.mk n).size + 1 := by
  rw [LubyTree.mk, LubyTree.size]
  grind
 
theorem size_is_two_sub_sizes_add_one' (n : Nat) :
    (LubyTree.mk n).wrap.size = 2 * (LubyTree.mk n).size + 1 := by
  simp [←size_is_two_sub_sizes_add_one]
  exact rfl

def LubyTree.valueAtSize (self : LubyTree) (s : Nat) (h1 : s ≤ self.size) : Nat := match h : self with
  | .leaf     => 1
  | .wrap sub =>
    if h2: self.size = s
    then 2 ^ self.depth.pred
    else
      if h3 : sub.size < s
      then
        have h1 : (s - sub.size) ≤ sub.size := by
          simp [size] at h1
          have : self.size = sub.size * 2 + 1 := by simp [h]; exact rfl
          simp [this] at h2
          have s2 : s ≤ sub.size * 2 := by grind
          have h' : sub.size ≤ s := by exact Nat.le_of_succ_le h3
          have : s ≤ sub.size + sub.size → s - sub.size ≤ sub.size := by
            exact fun a ↦ Nat.sub_le_of_le_add a
          apply this
          rw [←Nat.two_mul, Nat.mul_comm]
          exact s2
        sub.valueAtSize (s - sub.size) h1
      else
        have h2 : s ≤ sub.size := by grind 
        sub.valueAtSize s h2

def LubyTree.valueAt (s : Nat) : Nat :=
  let e := 2 ^ s
  have ep : e = value_of% e := rfl
  have h1 : s ≤ e := by
    simp [ep]
    induction s
    { grind }
    {
      expose_names
      simp at h
      simp [Nat.pow_add]
      simp [mul_two]
      refine Nat.add_le_add h ?_
      exact Nat.one_le_two_pow
    }
  have h2 : e ≤ (mk e).size := by
    induction e
    { simp }
    {
      expose_names
      simp [mk]
      simp [size]
      grind
    }
  have : s ≤ (mk e).size := by exact Nat.le_trans h1 h2
  (LubyTree.mk e).valueAtSize s this

#eval List.range 9 |>.map (fun n ↦ LubyTree.valueAt n.succ)

end Tree

