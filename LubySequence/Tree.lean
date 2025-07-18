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
  | sub (tree : LubyTree) : LubyTree
deriving BEq

def LubyTree.mk (level : Nat) : LubyTree := match level with
  | 0     => LubyTree.leaf
  | l + 1 => LubyTree.sub (LubyTree.mk l)

def LubyTree.toString (self : LubyTree) : String := match self with
  | .leaf => "leaf"
  | .sub (tree : LubyTree) => s!"↑{tree.toString}"

instance : ToString LubyTree where
  toString := LubyTree.toString

def t4 := LubyTree.mk 4
#eval t4 -- LubyTree.mk 4

def LubyTree.size (self : LubyTree) : Nat := match self with
  | .leaf => 1
  | .sub tree => tree.size * 2 + 1

#eval List.range 5 |>.map (fun n ↦ (LubyTree.mk n).size)

theorem size_is_two_sub_sizes_add_one (n : Nat) :
    (LubyTree.mk (n + 1)).size = 2 * (LubyTree.mk n).size + 1 := by
  rw [LubyTree.mk, LubyTree.size]
  grind

def LubyTree.valueAtSize (self : LubyTree) (s : Nat) (h1 : s ≤ self.size) : Nat := match self with
  | .leaf   => 0
  | .sub sb =>
    if h2: self.size = s
    then 0
    else
      if h3 : sb.size < s
      then
        have h1 : (s - sb.size) ≤ sb.size := by
          simp [size] at h1
          have : self.size = sb.size * 2 + 1 := by sorry
          simp [this] at h2
          have s2 : s ≤ sb.size * 2 := by sorry
          have h' : sb.size ≤ s := by exact Nat.le_of_succ_le h3
          have : s ≤ sb.size + sb.size → s - sb.size ≤ sb.size := by
            -- exact Nat.sub_lt_left_of_lt_add h' 
            sorry
          apply this
          rw [←Nat.two_mul, Nat.mul_comm]
          exact s2
        sb.valueAtSize (s - sb.size) h1
      else
        have h2 : s ≤ sb.size := by sorry 
        sb.valueAtSize s h2

end Tree

