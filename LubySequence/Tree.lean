import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

namespace LubyTree

inductive Tree where
  | leaf : Tree
  | tree (n : Nat) (sub : Tree) : Tree

end LubyTree


