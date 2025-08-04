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
#eval LubyTree.mk 0
#eval List.range 20 |>.map (fun n ↦ LubyTree.valueAt (n + 1) == Luby.luby n)

theorem LubyTree_is_Luby : ∀ n : Nat, LubyTree.valueAt (n + 1) = Luby.luby n := by
  intro n
  induction' n using Nat.strong_induction_on with n hn
  rw [Luby.luby]
  -- simp [LubyTree.valueAt]
  rw [LubyTree.valueAt.eq_def]
  split
  {
    -- case: Tree is leaf
    expose_names
    /- {
      -- case: Luby is stopped
      expose_names
      have : LubyTree.leaf = LubyTree.mk 0 := by rfl
      simp [this] at heq
      have : 2 ^ ((n + 1).size + 1) = 0 := by
        apply LubyTree.mk_unique at heq
        exact heq
      have : ∀ k : Nat, 2 ^ k ≠ 0 := by exact fun k ↦ Ne.symm (NeZero.ne' (2 ^ k))
      (expose_names; exact False.elim (this ((n + 1).size + 1) this_2))
    } -/
    {
      -- case: down recursively
      expose_names
      simp [Luby.S₂]
      have : LubyTree.leaf = LubyTree.mk 0 := by exact rfl
      -- simp [this] at heq
      -- apply LubyTree.mk_unique (2 ^ ((n + 1).size + 1)) 0 at heq
      -- have : ¬2 ^ ((n + 1).size + 1) = 0 := by exact NeZero.ne (2 ^ ((n + 1).size + 1))
      -- exact absurd heq this
      sorry
    }
  }
  sorry
  

#eval (LubyTree.mk 3).size

theorem LubyTree_is_Luby' : ∀ n : Nat, LubyTree.valueAt (n + 1) = Luby.luby n := by
  intro n
  induction' n using Nat.strong_induction_on with n hn
  rw [Luby.luby]
  split
  {
    expose_names
    have : Luby.S₂ (n + 2) = n + 2 → 2 ^ (n.size + 1) - 1 = n := by
      sorry
    sorry
   }
  sorry
