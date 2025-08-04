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

theorem LubyTree_is_Luby : ∀ n : Nat, LubyTree.luby (n + 1) = Luby.luby n := by
  intro n
  induction' n using Nat.strong_induction_on with n hn
  rw [LubyTree.luby, Luby.luby]
  split
  {
    simp [Luby.S₂]
    split
    {
      expose_names
      simp [LubyTree.enveloveDepth]
    }
    {
      expose_names
      simp [LubyTree.enveloveDepth]
      sorry
    }
  }
  {
    split
    {
      expose_names
      sorry
    }
    {
      expose_names
      sorry
    }
   }


theorem LubyTree_is_Luby' : ∀ n : Nat, LubyTree.valueAt (n + 1) = Luby.luby n := by
  intro n

  have le1 : 2 ≤ (n + 1 + 1).size := by
    have t1 : (2 : Nat).size ≤ (n + 1 + 1).size := by
      refine Nat.size_le_size ?_
      simp
    nth_rewrite 1 [Nat.size] at t1
    simp [Nat.binaryRec] at t1
    exact t1

  induction' n using Nat.strong_induction_on with n hn
  rw [Luby.luby]
  simp [LubyTree.valueAt]
  simp [LubyTree.valueAt.eq_def] at *
  split
  {
    -- case: at top
    expose_names
    rw [LubyTree.valueAtSize.eq_def]
    split
    {
      -- case: leaf
      expose_names
      have : LubyTree.leaf = LubyTree.mk 0 := by rfl
      simp [this] at heq
      have step1 : (n + 1 + 1).size - 1 = 0 := by exact LubyTree.mk_zero_is_leaf heq
      have step2 : (n + 1 + 1).size - 1 + 1 = 0 + 1 := by exact congrFun (congrArg HAdd.hAdd step1) 1
      have step3 : (n + 1 + 1).size - 1 + 1 = (n + 1 + 1).size := by
        refine Nat.sub_add_cancel ?_
        exact Nat.one_le_of_lt le1
      simp [step3] at step2
      have step4 : ¬1 = (n + 1 + 1).size := by exact Nat.ne_of_lt le1
      have step4 : ¬(n + 1 + 1).size = 1 := by exact fun a ↦ step4 (id (Eq.symm step2))
      exact absurd step2 step4
    } 
    {
      expose_names

      sorry
    }

    
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
