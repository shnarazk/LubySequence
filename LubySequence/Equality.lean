import Mathlib.Tactic
import LubySequence.Basic
import LubySequence.Tree
import LubySequence.Generator
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

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
      -- to show a conflict
      expose_names
      -- by `h` and `h_1`
      simp [LubyTree.is_envelove, LubyTree.enveloveSize, LubyTree.enveloveDepth] at h
      simp [LubyTree.enveloveDepth]
      simp [←length_of_bits_eq_size] at h
      have h' : n = 2 ^ (n + 1).bits.length - 2 := by
        exact Nat.eq_sub_of_add_eq (id (Eq.symm h))

      let a := (n + 1).bits.length
      have ap : a = value_of% a := by exact rfl
      have ap2 : 2 ^ a = n + 2 := by
        simp [ap]
        exact h
      simp [←ap] at h'
      have ap3 : (2 ^ a + 1).bits.length = a + 1 := by
        refine bitslength_add (by grind) (by grind)
      simp [ap2] at ap3
      have ap4 : 2 ^ (n + 2 + 1).bits.length = 2 ^ (a + 1) := by
        exact congrArg (HPow.hPow 2) ap3
      clear ap3
      have : 2 ^ (a + 1) = 2 * 2 ^ a := by exact Nat.pow_succ'
      simp [this] at ap4
      clear this
      have ap5 : 2 ^ (n + 2 + 1).bits.length / 2 = 2 * 2 ^ a / 2 := by
        exact congrFun (congrArg HDiv.hDiv ap4) 2
      clear ap4 
      have sl : 2 ^ (n + 2 + 1).bits.length / 2 = 2 ^ ((n + 2 + 1).bits.length - 1) := by
        refine Nat.div_eq_of_eq_mul_right (by grind) ?_
        refine Eq.symm (mul_pow_sub_one ?_ 2)
        refine Nat.pos_iff_ne_zero.mp ?_
        have t1 : (2 + 1).bits.length = 2 := by simp [Nat.bits, Nat.binaryRec]
        have t2 : 0 < 2 := by grind
        have t3 : (2 + 1).bits.length ≤ (n + 2 + 1).bits.length := by
          refine bitslength_le_bitslength (by grind)
        simp [t1] at t3
        exact Nat.zero_lt_of_lt t3
      simp [sl] at ap5
      have ap6 : 2 ^ ((n + 2 + 1).bits.length - 1) = 2 ^ a := by
        exact congrArg (HPow.hPow 2) ap5
      clear ap5
      simp [ap2] at ap6
      simp [←length_of_bits_eq_size] at h_1
      exact absurd ap6 h_1
    }
  }
  {
    split
    {
      expose_names
      simp [LubyTree.is_envelove, LubyTree.enveloveSize, LubyTree.enveloveDepth] at h
      simp [Luby.S₂] at h_1
      expose_names
      have c1 : 2 ^ ((n + 2 + 1).size - 1) = 2 ^ (n + 1).size := by
        have t1 : (n + 2 + 1).size - 1 = (n + 1).size := by
          simp [←length_of_bits_eq_size]

          sorry
        have t1' : 2 ^ ((n + 2 + 1).size - 1) = 2 ^ (n + 1).size := by exact congrArg (HPow.hPow 2) t1
        exact t1'
      simp [h_1] at c1
      have : 2 ^ (n + 1).size = n + 2 := by exact id (Eq.symm c1)
      exact absurd this h 
    }
    {
      expose_names
      simp [Luby.S₂, LubyTree.quotient]
      have : n % ((2 ^ (n + 1).size - 1 - 1) / 2) = n + 1 - 2 ^ ((n + 1).size - 1) := by
        sorry
      simp [this]
      have : n + 1 - 2 ^ ((n + 1).size - 1) < n := by sorry
      have hn' := hn (n + 1 - 2 ^ ((n + 1).size - 1)) this
      exact hn'
    }
   }

/-
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
 -/ 

#eval (LubyTree.mk 3).size

/-
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
  -/
