import Mathlib.Tactic
import LubySequence.Basic
import LubySequence.Tree
import LubySequence.Generator

open Tree

#eval List.range 24 |>.map (fun n ↦ LubyTree.valueAt (n + 1))
#eval List.range 24 |>.map (fun n ↦ Luby.luby n)
#eval LubyTree.mk 0
#eval LubyTree.valueAt 1
#eval (1 : Nat).bits

theorem LubyTree_is_Luby : ∀ n : Nat, LubyTree.valueAt (n + 1) = Luby.luby n := by
  intro n
  induction' n using Nat.strong_induction_on with n hn
  simp [LubyTree.valueAt]
  rw [LubyTree.valueAtSize.eq_def]
  rw [Luby.luby]
  split
  {
    expose_names
    split
    {
      expose_names
      have : LubyTree.leaf = LubyTree.mk 0 := by rfl
      simp [this] at heq
      have : 2 ^ ((n + 1).size + 1) = 0 := by
        apply LubyTree.mk_unique at heq
        exact heq
      have : ∀ k : Nat, 2 ^ k ≠ 0 := by exact fun k ↦ Ne.symm (NeZero.ne' (2 ^ k))
      (expose_names; exact False.elim (this ((n + 1).size + 1) this_2))
    }
    {
      expose_names
      simp [Luby.S₂]
      sorry

    }





  }
  {
    sorry
   }

