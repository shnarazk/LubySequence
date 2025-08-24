import Mathlib.Tactic
import LubySequence.Basic
import LubySequence.Tree
import LubySequence.State
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size

open Tree

#eval List.range 24 |>.map (fun n ↦ LubyTree.valueAt (n + 1))
#eval List.range 24 |>.map (fun n ↦ Luby.luby n)
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
      simp [LubyTree.envelopeDepth]
    }
    {
      -- to show a conflict
      expose_names
      -- by `h` and `h_1`
      simp [LubyTree.is_envelope, LubyTree.envelopeSize, LubyTree.envelopeDepth] at h
      simp [LubyTree.envelopeDepth]
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
      simp [Luby.is_envelope] at h_1
      exact absurd ap6 h_1
    }
  }
  {
    expose_names
    split
    {
      simp [LubyTree.is_envelope, LubyTree.envelopeSize, LubyTree.envelopeDepth] at h
      simp [Luby.S₂] at *
      expose_names
      let a := (n + 2 + 1).size
      have ap : a = value_of% a := by exact rfl
      have ap2 : n = 2 ^ (a - 1) - 2 := by
        simp [Luby.is_envelope, Luby.S₂] at h_2
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
        have c : LubyTree.is_envelope (n + 1) = true := by
          simp [nlim, LubyTree.is_envelope, LubyTree.envelopeSize, LubyTree.envelopeDepth]
        exact absurd c h
      have nsize_lower : 1 ≤ n.size := by
        have t1 : Nat.size 1 = 1 := by exact Nat.size_one
        have t2 : Nat.size 1 ≤ n.size := by exact Nat.size_le_size n_lower
        exact le_of_eq_of_le (id (Eq.symm t1)) t2
      simp [Luby.S₂, LubyTree.quotient]
      have n_upper : 2 ^ (n + 1).size ≠ n + 2 := by
        by_contra nlim
        have c : LubyTree.is_envelope (n + 1) = true := by
          simp [LubyTree.is_envelope, LubyTree.envelopeSize, LubyTree.envelopeDepth]
          exact nlim
        exact absurd c h
      have n1size1 : 2 ≤ (n + 1).size := by
        have t1 : (1 + 1).size ≤ (n + 1).size := by
          refine Nat.size_le_size ?_
          exact Nat.add_le_add_right n_lower 1
        have t2 : (1 + 1).size = 2 := by
          simp [Nat.size, Nat.binaryRec]
        simp [t2] at t1
        exact t1
      have ind : n % ((2 ^ (n + 1).size - 1 - 1) / 2) = n + 1 - 2 ^ ((n + 1).size - 1) := by
        -- n には下限がある。求めよ。また上限もある。この場合modは減算になる。
        have low : 2 ^ (n + 1).size ≤ 2 * (n + 1) := by
          /- 両者の桁数は同じはず。その上で左辺がその桁数で表される最小の
           - 数であることから証明可能。
          -/
          -- 両辺の桁は等しい
          have size_restriction : (2 ^ (n + 1).size).size = (2 * (n + 1)).size := by
            have left : (2 ^ (n + 1).size).size = (n + 1).size + 1 := by
              exact Nat.size_pow
            simp [left]
            have right : (2 * (n + 1)).size = (n + 1).size + 1 := by
              refine size_of_double_eq_self_add_one (n + 1) ?_
              exact Nat.add_pos_left n_lower 1
            simp [right]
          have sr' : (2 ^ (n + 1).size).size = (n + 1).size + 1 := by
            exact Nat.size_pow
          simp [sr'] at size_restriction
          have sr : (2 * (n + 1)).size = (n + 1).size + 1 := by
            exact id (Eq.symm size_restriction)
          -- 桁が等しい全ての数は左辺以上である。
          have left_is_smallest {x k : Nat} (h : x.size = k + 1) : 2 ^ k ≤ x := by
            by_contra c
            simp at c
            have c1 := pow2_is_minimum k x c
            have c1' : x.size < k + 1 := by exact Order.lt_add_one_iff.mpr c1
            have c1'' : ¬x.size = k + 1 := by exact Nat.ne_of_lt c1'
            exact absurd h c1''
          have applied := left_is_smallest sr
          exact applied

        -- rw [div_two] at low
        simp [mul_add] at low
        apply Nat.sub_le_of_le_add at low
        have low' : 2 ^ (n + 1).size - 1 - 1 ≤ 2 * n := by exact low
        have low'' : (2 ^ (n + 1).size - 1 - 1) / 2 ≤ n := by
          exact Nat.div_le_of_le_mul low
        clear low low'
        have high : n < (2 ^ (n + 1).size - 1 - 1) / 2 * 2 := by
          have s1 : (2 ^ (n + 1).size - 1 - 1) / 2 * 2 = (2 ^ (n + 1).size - 2) / 2 * 2 := by
            exact rfl
          simp [s1]
          clear s1
          have s2 : (2 ^ (n + 1).size - 2) / 2 * 2 = 2 ^ (n + 1).size - 2 := by
            refine Nat.div_mul_cancel ?_
            refine Nat.dvd_sub ?_ (by grind)
            {
              refine dvd_pow (by grind) ?_
              { exact Nat.ne_zero_of_lt n1size1 }
            }
          simp [s2]
          apply Nat.lt_sub_of_add_lt
          have t1 : n + 1 < 2 ^ (n + 1).size := by exact Nat.lt_size_self (n + 1)
          have t1' : n + 2 ≤ 2 ^ (n + 1).size := by exact t1
          have t2 : n + 2 < 2 ^ (n + 1).size := by
            exact Nat.lt_of_le_of_ne t1 (id (Ne.symm n_upper))
          exact t2
        -- have high : n ≤ 2 ^ ((n + 1).size - 1 - 1) / 2 := by
        have mod {a b : Nat} (h : 0 < a) (h1 : a ≤ b) (h2 : b < a * 2) :
            b % a = b - a := by
          let d := b - a
          have dp : d = value_of% d := by exact rfl
          have ap1 : d < a := by
            refine Nat.sub_lt_left_of_lt_add h1 ?_
            simp [mul_two] at h2
            exact h2
          have : b = a + d := by exact Eq.symm (Nat.add_sub_of_le h1)
          nth_rewrite 1 [this]
          have : (a + d) % a = d % a := by exact Nat.add_mod_left a d
          simp [this, ←dp]
          exact Nat.mod_eq_of_lt ap1
        have g := mod (by grind) low'' high
        simp [g]
        have left : n - (2 ^ (n + 1).size - 1 - 1) / 2 = n + 1 - 2 ^ (n + 1).size / 2 := by
          have s1 : (2 ^ (n + 1).size - 1 - 1) / 2 = (2 ^ (n + 1).size - 2) / 2 := by
            exact rfl
          simp [s1]
          clear s1
          have s2 : (2 ^ (n + 1).size - 2) / 2 = 2 ^ (n + 1).size / 2 - 2 / 2 := by
            refine Eq.symm (Nat.sub_eq_of_eq_add ?_)
            refine Nat.div_eq_sub_div (by grind) ?_
            refine Nat.le_pow ?_
            exact Nat.zero_lt_of_lt n1size1
          simp [s2]
          refine Nat.sub_sub_right n ?_
          refine (Nat.one_le_div_iff (by grind)).mpr ?_
          refine Nat.le_self_pow ?_ 2
          have t1 : (1 + 1).size ≤ (n + 1).size := by
            refine Nat.size_le_size ?_
            exact Nat.add_le_add_right n_lower 1
          have t2 : (1 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
          simp [t2] at t1
          exact Nat.ne_zero_of_lt t1
        have right : n + 1 - 2 ^ ((n + 1).size - 1) = n + 1 - 2 ^ (n + 1).size / 2 := by
          have : 2 ^ ((n + 1).size - 1) = 2 ^ (n + 1).size / 2 := by
            refine Eq.symm (Nat.div_eq_of_eq_mul_right ?_ ?_)
            { grind }
            {
              refine Eq.symm (mul_pow_sub_one ?_ 2)
              have t1 : 0 < (1 + 1).size := by simp [Nat.size, Nat.binaryRec]
              have t2 : (1 + 1).size ≤ (n + 1).size := by
                refine Nat.size_le_size ?_
                exact Nat.add_le_add_right n_lower 1
              have : 0 < (n + 1).size := by exact Nat.lt_of_lt_of_le t1 t2
              have : (n + 1).size ≠ 0 := by exact Nat.ne_zero_of_lt this
              exact this
            }
          simp [this]
        simp [left, right]
      simp [ind]
      have tf : n = 0 ∨ ¬n = 0 := by exact eq_or_ne _ _
      rcases tf with t|f
      {
        simp [t] at *
        -- simp [LubyTree.is_envelope, LubyTree.envelopeSize, LubyTree.envelopeDepth] at h
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

#eval List.range 30 |>.map (fun n ↦ ((LubyState.ofNat n).luby, (LubyState.ofNat n).segment_height, LubyTree.luby (n + 1)))

/- TODO: And we have to prove LubyTree.luby is equivalent to f(LubyTree.depth).
theorem LubyState_segIx_is_tree_depth : ∀ n : Nat, (LubyState.ofNat n).segIx = LubyTree.envelopeDepth (n + 1) := by
  -- sapply?
  sorry -/

#eval List.range 30 |>.map (fun n ↦ (Luby.luby n, (LubyState.ofNat n).luby))

theorem LubyState_is_Luby : ∀ n : Nat, Luby.luby n = (LubyState.ofNat n).luby := by
  intro n
  sorry

/-
  induction' n using Nat.strong_induction_on with n hn
  -- 先に場合分けをしてしまおう
  have tree_cases : LubyTree.is_envelope (n + 1) = true ∨ LubyTree.is_envelope (n + 1) = false := by
    exact Bool.eq_false_or_eq_true (LubyTree.is_envelope (n + 1))
  have gen_cases : (LubyState.ofNat n).is_envelope ∨ ¬(LubyState.ofNat n).is_envelope := by
    exact eq_or_ne (LubyState.ofNat n).is_envelope true
  simp [LubyTree.is_envelope, LubyTree.envelopeSize, LubyTree.envelopeDepth] at tree_cases
  -- simp [LubyState.is_envelope] at gen_cases
  rcases tree_cases with tree_env|not_tree_env
  {
    rcases gen_cases with gen_env|not_gen_env
    {
      sorry
    }
    {
      sorry
    }
  }
  {
    rcases gen_cases with gen_env|not_gen_env
    {
      sorry
    }
    {
      sorry
    }
  }

  split
  {
    expose_names
    rw [←LubyTree.luby, LubyState.ofNat, LubyState.luby]
    have tf : n = 0 ∨ n > 0 := by exact Nat.eq_zero_or_pos n
    rcases tf with t|f
    {
      simp [t] at *
      simp [LubyTree.envelopeDepth]
      simp [default, LubyState.zero, LubyState.next]
    }
    {
      -- have hn' := hn 0
      -- rw [LubyTree.luby] at hn'
      simp only [LubyTree.envelopeDepth]
      -- envelopeなら$n = 2 ^ i - 1$, またsegIxが式として表されるはず。
      -- こんなことをする必要はない。envelopなのだから再帰せずに値が求まる
      have s1 : (LubyState.ofNat n).is_envelope := by
        simp [LubyTree.is_envelope, LubyTree.envelopeSize, LubyTree.envelopeDepth] at h
        simp [LubyState.is_envelope]
        have : (n - 1) / 2 < n := by
          have : n - 1 < 2 * n := by
            have : n < 2 * n + 1 := by
              have : n < n + n + 1 := by
                have : 0 < n + 1 := by exact Nat.add_pos_left f 1
                refine Nat.lt_add_right 1 ?_
                exact Nat.lt_add_of_pos_right f
              have t : 2 * n = n + n := by exact Nat.two_mul n
              simp [←t] at this
              exact this
            exact Nat.sub_lt_right_of_lt_add f this
          exact Nat.div_lt_of_lt_mul this
        have hn' := hn ((n - 1) / 2) this
        sorry

      have s2 : (LubyState.ofNat n).locIx = (n + 1).size - 1 := by sorry
      have s3 : LubyState.ofNat n = LubyState.zero.next n := by exact rfl
      simp [s3] at s2
      simp [s2]
    }
  }
  sorry

theorem LubyState_is_Luby' : ∀ n : Nat, (LubyState.ofNat n).luby = Luby.luby n := by
  intro n
  induction' n /- using Nat.strong_induction_on -/ with n hn
  {
    simp [LubyState.ofNat, LubyState.zero, LubyState.luby, default, LubyState.next]
    rw [Luby.luby, Luby.S₂]
    simp [Nat.size, Nat.binaryRec, Luby.S₂]
  }
  {
    -- simp [LubyState.ofNat, LubyState.zero]
    have : LubyState.ofNat (n + 1) = (LubyState.ofNat n).next := by exact rfl
    simp [this]
    sorry
 }
-/
