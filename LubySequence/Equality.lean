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
      have h' : n = 2 ^ (n + 1).size - 2 := by
        exact Nat.eq_sub_of_add_eq (id (Eq.symm h))

      let a := (n + 1).size
      have ap : a = value_of% a := by exact rfl
      have ap2 : 2 ^ a = n + 2 := by
        simp [ap]
        exact h
      simp [←ap] at h'
      have ap3 : (2 ^ a + 1).size = a + 1 := by
        refine size_add (by grind) (by grind)
      simp [ap2] at ap3
      have ap4 : 2 ^ (n + 2 + 1).size = 2 ^ (a + 1) := by
        exact congrArg (HPow.hPow 2) ap3
      clear ap3
      have : 2 ^ (a + 1) = 2 * 2 ^ a := by exact Nat.pow_succ'
      simp [this] at ap4
      clear this
      have ap5 : 2 ^ (n + 2 + 1).size / 2 = 2 * 2 ^ a / 2 := by
        exact congrFun (congrArg HDiv.hDiv ap4) 2
      clear ap4
      have sl : 2 ^ (n + 2 + 1).size / 2 = 2 ^ ((n + 2 + 1).size - 1) := by
        refine Nat.div_eq_of_eq_mul_right (by grind) ?_
        refine Eq.symm (mul_pow_sub_one ?_ 2)
        refine Nat.pos_iff_ne_zero.mp ?_
        have t1 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
        have t2 : 0 < 2 := by grind
        have t3 : (2 + 1).size ≤ (n + 2 + 1).size := by
          refine Nat.size_le_size (by grind)
        simp [t1] at t3
        exact Nat.zero_lt_of_lt t3
      simp [sl] at ap5
      have ap6 : 2 ^ ((n + 2 + 1).size - 1) = 2 ^ a := by
        exact congrArg (HPow.hPow 2) ap5
      clear ap5
      simp [ap2] at ap6
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
      let a := (n + 2 + 1).size
      have ap : a = value_of% a := by exact rfl
      have ap2 : n = 2 ^ (a - 1) - 2 := by
        simp [←ap] at h_2
        exact Nat.eq_sub_of_add_eq (id (Eq.symm h_2))
      have ap3 : 2 ≤ a := by
        have step1 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
        have step2 : (2 + 1).size ≤ (n + 2 + 1).size := by
          refine Nat.size_le_size ?_
          grind
        simp [step1, ←ap] at step2
        exact step2
      have : 2 ^ (n + 1).size = n + 2 := by
        have : 2 ^ (2 ^ (a - 1) - 2 + 1).size = 2 ^ (a - 1) - 2 + 2 := by
          have left : 2 ^ (2 ^ (a - 1) - 2 + 1).size = 2 ^ (a - 1) := by
            have : (2 ^ (a - 1) - 2 + 1).size = a - 1 := by
              have : (2 ^ (a - 1) - 1).size = a - 1 := by
                refine size_sub ?_ (by grind) ?_
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
      have n_lower : 1 ≤ n := by
        by_contra nlim
        simp at nlim
        have c : LubyTree.is_envelove (n + 1) = true := by
          simp [nlim, LubyTree.is_envelove, LubyTree.enveloveSize, LubyTree.enveloveDepth]
        exact absurd c h
      have nsize_lower : 1 ≤ n.size := by
        have t1 : Nat.size 1 = 1 := by exact Nat.size_one
        have t2 : Nat.size 1 ≤ n.size := by exact Nat.size_le_size n_lower
        exact le_of_eq_of_le (id (Eq.symm t1)) t2
      simp [Luby.S₂, LubyTree.quotient]
      have ind : n % ((2 ^ (n + 1).size - 1 - 1) / 2) = n + 1 - 2 ^ ((n + 1).size - 1) := by
        -- n には下限がある。求めよ。また上限もある。この場合modは減算になる。
        have low : 2 ^ ((n + 1).size - 1 - 1) / 2 ≤ n := by
          have n1upto : (n + 1).size ≤ n.size + 1 := by
            have s1 : n + 1 ≤ 2 * n := by exact add_one_le_two_mul n_lower
            have s2 : (n + 1).size ≤ (2 * n).size := by exact Nat.size_le_size s1
            have s3 : (2 * n).size = n.size + 1 := by
              exact size_of_double_eq_self_add_one n n_lower
            simp [s3] at s2
            exact s2
          have goal1 : 2 ^ ((n + 1).size - 1 - 1) ≤ 2 * n := by 
            have s1 : (2 ^ ((n + 1).size - 1 - 1)).size < (2 * n).size := by
              have left : (2 ^ ((n + 1).size - 1 - 1)).size = (n + 1).size - 1 - 1 + 1 := by
                exact Nat.size_pow
              have right : (2 * n).size = n.size + 1 := by
                exact size_of_double_eq_self_add_one n n_lower
              simp [left, right]
              have n1upto' : (n + 1).size - 1 ≤ n.size := by
                exact Nat.sub_le_of_le_add n1upto
              refine Nat.sub_one_lt_of_le ?_ n1upto'
              have cngr1 : (1 + 1).size ≤ (n + 1).size := by
                refine Nat.size_le_size ?_
                exact Nat.add_le_add_right n_lower 1
              have cngr2 : (1 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
              simp [cngr2] at cngr1
              grind
            have : 2 ^ ((n + 1).size - 1 - 1) < 2 * n := by exact le_if_le_size s1
          exact Nat.div_le_of_le_mul goal1
        have high : n < 2 ^ (n + 1).size - 1 := by
          sorry
        sorry
      simp [ind]
      have tf : n = 0 ∨ ¬n = 0 := by exact eq_or_ne _ _
      rcases tf with t|f
      {
        simp [t] at *
        -- simp [LubyTree.is_envelove, LubyTree.enveloveSize, LubyTree.enveloveDepth] at h
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

