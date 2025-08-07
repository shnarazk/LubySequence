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
    expose_names
    split
    {
      simp [LubyTree.is_envelove, LubyTree.enveloveSize, LubyTree.enveloveDepth] at h
      simp [Luby.S₂] at *
      expose_names
      simp [←length_of_bits_eq_size] at *
      let a := (n + 2 + 1).bits.length
      have ap : a = value_of% a := by exact rfl
      have ap2 : n = 2 ^ (a - 1) - 2 := by
        simp [←ap] at h_2
        exact Nat.eq_sub_of_add_eq (id (Eq.symm h_2))
      have ap3 : 2 ≤ a := by
        have step1 : (2 + 1).bits.length = 2 := by simp [Nat.bits, Nat.binaryRec]
        have step2 : (2 + 1).bits.length ≤ (n + 2 + 1).bits.length := by
          refine bitslength_le_bitslength ?_
          grind
        simp [step1, ←ap] at step2
        exact step2
      have : 2 ^ (n + 1).bits.length = n + 2 := by
        have : 2 ^ (2 ^ (a - 1) - 2 + 1).bits.length = 2 ^ (a - 1) - 2 + 2 := by 
          have left : 2 ^ (2 ^ (a - 1) - 2 + 1).bits.length = 2 ^ (a - 1) := by 
            have : (2 ^ (a - 1) - 2 + 1).bits.length = a - 1 := by
              have : (2 ^ (a - 1) - 1).bits.length = a - 1 := by
                refine bitslength_sub ?_ (by grind) ?_
                { refine Nat.zero_lt_sub_of_lt (by grind) }
                { exact Nat.one_le_two_pow }
              have eq1 : 2 ^ (a - 1) - 2 + 1 = 2 ^ (a - 1) - 1 := by
                refine Eq.symm (Nat.eq_add_of_sub_eq ?_ rfl)
                have : 2 ≤ 2 ^ (a - 1) := by
                  refine Nat.le_pow ?_
                  exact Nat.zero_lt_sub_of_lt ap3
                exact Nat.le_sub_one_of_lt this
              simp [eq1]
              exact this
            exact congrArg (HPow.hPow 2) this
          have right : 2 ^ (a - 1) - 2 + 2 = 2 ^ (a - 1) := by
            refine Nat.sub_add_cancel ?_
            refine Nat.le_pow ?_
            exact Nat.zero_lt_sub_of_lt ap3
          simp [left, right]
        simp [←ap2] at this
        exact this
      exact absurd this h
    }
    {
      expose_names
      simp [Luby.S₂, LubyTree.quotient]
      have : n % ((2 ^ (n + 1).size - 1 - 1) / 2) = n + 1 - 2 ^ ((n + 1).size - 1) := by
        sorry
      simp [this]
      have tf : n = 0 ∨ ¬n = 0 := by exact eq_or_ne _ _
      rcases tf with t|f
      {
        simp [t] at *
        simp [LubyTree.is_envelove, LubyTree.enveloveSize, LubyTree.enveloveDepth] at h
      }
      have : n + 1 - 2 ^ ((n + 1).size - 1) < n := by
        have : 1 < 2 ^ ((n + 1).size - 1) := by
          have step1 : 2 < 2 ^ (n + 1).size := by
            have s1 : 1 ≤ n := by exact Nat.one_le_iff_ne_zero.mpr f
            have s2 : 1 + 1 ≤ n + 1 := by exact Nat.add_le_add_right s1 1
            have s3 : 2 ^ (1 + 1).size ≤ 2 ^ (n + 1).size := by
              refine Luby.pow2_le_pow2 (1 + 1).size (n + 1).size ?_
              exact Nat.size_le_size s2
            have : 2 ^ (1 + 1).size = 4 := by
              simp only [Nat.reduceAdd]
              simp [Nat.size, Nat.binaryRec]
            simp [this] at s3
            exact Nat.lt_of_add_left_lt s3
          have step2 : 2 / 2 < 2 ^ (n + 1).size / 2 := by
            refine Nat.div_lt_div_of_lt_of_dvd ?_ step1
            refine Dvd.dvd.pow ?_ ?_
            exact (Nat.minFac_eq_two_iff 2).mp rfl
            have t1 : 0 < (1 : Nat).size := by simp [Nat.size]
            have t2 : (1 : Nat).size ≤ (n + 1).size := by
              refine Nat.size_le_size ?_
              exact Nat.le_add_left 1 n
            have : 0 < (n + 1).size := by exact Nat.lt_of_lt_of_le t1 t2
            exact Nat.ne_zero_of_lt this
          simp at step2
          have right : 2 ^ (n + 1).size / (2 ^ 1) = 2 ^ ((n + 1).size - 1) := by
            refine Nat.pow_div ?_ (by grind)
            have t1 : Nat.size 1 ≤ (n + 1).size := by
              refine Nat.size_le_size ?_
              exact Nat.le_add_left 1 n
            have t2 : Nat.size 1 = 1 := by exact Nat.size_one
            simp [t2] at t1
            exact t1
          simp at right
          simp only [right] at step2
          exact step2
        have t1 : n + 1 < n + 2 ^ ((n + 1).size - 1) := by exact Nat.add_lt_add_left this n
        have t2 : 2 ^ ((n + 1).size - 1) ≤ n + 1 := by
          refine Nat.lt_size.mp ?_
          refine Nat.sub_one_lt ?_
          have t1 : Nat.size 1 = 1 := by exact Nat.size_one
          have t2 : Nat.size 1 ≤ (n + 1).size := by
            refine Nat.size_le_size ?_
            exact Nat.le_add_left 1 n
          simp [t1] at t2
          exact Nat.ne_zero_of_lt t2
        exact Nat.sub_lt_right_of_lt_add t2 t1
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
