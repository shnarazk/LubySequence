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
  | sub tree => tree.size * 2 + 1

#eval List.range 5 |>.map (fun n ↦ (LubyTree.mk n).size)

theorem size_is_two_sub_sizes_add_one (n : Nat) :
    (LubyTree.mk n).size = 2 * (LubyTree.mk n).sub.size + 1 := by
  sorry

def LubyTree.valueAtSize (self : LubyTree) (n : Nat) (h : n ≤ self.size) : Nat := match self with
  | .leaf    => 0
  | .sub sb =>
    if h' : sb.size < n
    then
      have h1 : (n - sb.size) ≤ sb.size := by sorry 
      sb.valueAtSize (n - sb.size) h1
    else
      have h2 : n ≤ sb.size := by sorry 
      sb.valueAtSize n h2
-- termination_by self

end Tree

