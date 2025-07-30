import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Utils

namespace Tree

/-
 - The level of LubyTrees starts with 1.
 - The index of the elements of LubyTree starts with 0.
 -/

inductive LubyTree where
  | leaf : LubyTree
  | wrap (tree : LubyTree) : LubyTree
deriving BEq

def LubyTree.mk (level : Nat) : LubyTree := match level with
  | 0     => LubyTree.leaf
  | l + 1 => wrap (LubyTree.mk l)

def LubyTree.toString (self : LubyTree) : String := match self with
  | .leaf => "leaf"
  | wrap (tree : LubyTree) => s!"↑{tree.toString}"

instance : ToString LubyTree where
  toString := LubyTree.toString

def t4 := LubyTree.mk 4
#eval t4 -- LubyTree.mk 4

theorem LubyTree.wrap_is_congruent (t1 t2 : LubyTree) : t1.wrap = t2.wrap ↔ t1 = t2 := by
  constructor
  {
    intro h
    simp at h
    exact h
  }
  {
    intro h
    simp
    exact h
  }

def LubyTree.depth (self : LubyTree) : Nat := match self with
  | .leaf => 1
  | wrap tree => tree.depth + 1

theorem LubyTree.depth_gt_one : ∀ t : LubyTree, t.depth ≥ 1 := by
  intro t
  induction t <;> simp [LubyTree.depth]

theorem LubyTree.mk_of_depth_eq_self (t : LubyTree) : LubyTree.mk (t.depth - 1) = t := by
  induction t with
  | leaf => simp [LubyTree.depth, LubyTree.mk]
  | wrap sub =>
    expose_names
    simp [LubyTree.depth]
    rw [LubyTree.mk.eq_def]
    split
    {
      expose_names
      have this := LubyTree.depth_gt_one sub
      have : ¬sub.depth = 0 := by exact Nat.ne_zero_of_lt this
      exact absurd heq this
    }
    {
      expose_names
      have : sub.depth - 1 = l.succ - 1 := by exact congrFun (congrArg HSub.hSub heq) 1
      have : sub.depth - 1 = l := by exact this
      simp [←this, tree_ih]
    }

#eval LubyTree.mk 0
#eval LubyTree.leaf.depth

theorem LubyTree.mk_self_eq_depth_add_one (n: Nat) : (LubyTree.mk n).depth = n + 1 := by
  induction n with
  | zero => 
    simp [LubyTree.mk]
    rfl
  | succ n ih =>
    simp [LubyTree.mk]
    simp [LubyTree.depth]
    exact ih

theorem LubyTree.mk_zero_is_leaf {n : Nat} : LubyTree.mk n = LubyTree.leaf → n = 0 := by
  induction' n with n hn
  {
    intro h
    simp [mk] at h
    exact rfl
  }
  {
    intro h
    simp [mk] at h
  }

theorem LubyTree.wrap_n_eq_n_add_one (n : Nat) : LubyTree.wrap (LubyTree.mk n) = LubyTree.mk (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [←ih]
    nth_rw 2 [LubyTree.mk.eq_def]
    split
    {
      expose_names
      have (n : Nat) : n + 1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one n)
      have hne := this (n + 1)
      exact absurd heq hne
    }
    {
      expose_names
      have : n + 1 = l := by exact Nat.succ_inj.mp heq
      rw [←this]
      simp [ih]
    }

theorem LubyTree.mk_unique (m n : Nat) : LubyTree.mk m = LubyTree.mk n → m = n := by
  induction m generalizing n with
  | zero =>
    intro z
    simp [mk] at z
    have h := Eq.symm z
    apply LubyTree.mk_zero_is_leaf at h
    grind
  | succ m hm =>
    intro h
    have tf : n = 0 ∨ ¬n = 0 := by exact eq_or_ne _ _
    rcases tf with t|f
    { simp [t,mk] at h }  
    {
      have : n = (n - 1) + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero f)
      rw [this] at h
      rw [←LubyTree.wrap_n_eq_n_add_one] at h
      rw [←LubyTree.wrap_n_eq_n_add_one] at h
      have : mk m = mk (n - 1) := by
        exact (wrap_is_congruent (mk m) (mk (n - 1))).mp h
      have h' := hm (n - 1) this
      grind
   }

theorem LubyTree.unwrap_wrap_self_eq_self (d : Nat) (t : LubyTree) :
    LubyTree.mk (d + 1) = t.wrap ↔ LubyTree.mk d = t := by
  constructor
  {
    intro h
    simp [LubyTree.mk] at h
    exact h
  }
  {
    intro h
    simp [LubyTree.mk]
    exact h
  }

def LubyTree.size (self : LubyTree) : Nat := match self with
  | .leaf => 1
  | wrap tree => tree.size * 2 + 1

#eval List.range 5 |>.map (fun n ↦ (LubyTree.mk n).size)

theorem LubyTree.size_ge_one (t : LubyTree) : t.size ≥ 1 := by
  induction t <;> simp [LubyTree.size]

theorem size_is_two_sub_sizes_add_one (n : Nat) :
    (LubyTree.mk (n + 1)).size = 2 * (LubyTree.mk n).size + 1 := by
  rw [LubyTree.mk, LubyTree.size]
  grind
 
theorem size_is_two_sub_sizes_add_one' (n : Nat) :
    (LubyTree.mk n).wrap.size = 2 * (LubyTree.mk n).size + 1 := by
  simp [←size_is_two_sub_sizes_add_one]
  exact rfl

#eval Nat.bits (2 * 5)

theorem length_of_bits_eq_size (n : Nat) : n.bits.length = n.size := by
  exact Nat.size_eq_bits_len n

theorem bits_of_double_eq_cons_false_and_bits (n : Nat) (h : n > 0) :
    (2 * n).bits = false :: n.bits := by
  have : n ≠ 0 := by exact Nat.ne_zero_of_lt h
  exact Nat.bit0_bits n this

example (n : Nat) : (2 * n + 1).bits = true :: n.bits := by
  exact Nat.bit1_bits n

theorem size_of_two_mul_eq_aize_add_one (n : Nat) (h : n > 0) :
    n.size + 1 = (n * 2).size := by
  simp [←Nat.size_eq_bits_len, Nat.mul_comm n 2, bits_of_double_eq_cons_false_and_bits n h]

theorem depth_and_size (tree : LubyTree) : tree.depth = tree.size.size := by
  induction tree
  { simp [LubyTree.depth, LubyTree.size] }
  {
    expose_names
    simp [LubyTree.depth]
    simp [LubyTree.size]
    simp [tree_ih]
    simp [←length_of_bits_eq_size, Nat.mul_comm tree.size 2]
  }

/-
 - The envelope is the smallest tree containing `s` elements.
 -/
def LubyTree.enveloveDepth (s : Nat) : Nat := s.size
def LubyTree.enveloveSize (s : Nat) : Nat := 2 ^ (LubyTree.enveloveDepth s) - 1
def LubyTree.envelove (s : Nat) : LubyTree := LubyTree.mk (LubyTree.enveloveDepth s - 1)
def LubyTree.is_envelove (s : Nat) : Bool := LubyTree.enveloveSize s = s
def LubyTree.quotientOfSize (s : Nat) (e : Nat) := (s - 1) % ((e - 1) / 2) + 1
def LubyTree.quotient (s : Nat) := (s - 1) % (((2 ^ s.size - 1) - 1) / 2) + 1

#eval List.range 20 |>.map (fun n ↦ (n + 1, LubyTree.enveloveDepth (n + 1)))
#eval List.range 20 |>.map (fun n ↦ (n + 1, LubyTree.enveloveSize (n + 1), LubyTree.is_envelove (n + 1)))
#eval LubyTree.quotientOfSize 2 3
#eval LubyTree.is_envelove 2
#eval LubyTree.enveloveSize 2
#eval LubyTree.is_envelove 1
#eval LubyTree.is_envelove 0

-- This is impossible
-- theorem LubyTree.quotient_is_decreasing : ∀ n ≥ 2, n > LubyTree.quotient n := by 

theorem LubyTree.envelop_of_quotient_is_desceasing :
    ∀ n ≥ 2, n < (2 ^ n.size - 1 - 1) / 2 → LubyTree.enveloveSize n > 2 * (LubyTree.quotient n) := by
  intro n hn h
  simp only [LubyTree.quotient, LubyTree.enveloveSize, LubyTree.enveloveDepth]
  have s2 : Nat.size 2 = 2 := by simp [Nat.size, Nat.binaryRec]
  have le2 : (2 : Nat).size ≤ n.size := by exact Nat.size_le_size hn
  have le2' : 2 ≤ (2 : Nat).size := by exact Nat.le_of_eq (id (Eq.symm s2))
  have le2n : 2 ≤ n.size := by exact Nat.le_trans le2' le2
  have tr1 : 2 ≤ 2 ^ (2 : Nat).size - 1 - 1 := by
    have : (2 : Nat).size = 2 := by simp [Nat.size, Nat.binaryRec]
    simp [this]
  have s3 : 2 ^ (2 : Nat).size - 1 - 1 ≤ 2 ^ n.size - 1 - 1 := by
    have : 2 ^ (2 : Nat).size ≤ 2 ^ n.size := by
      refine (Nat.pow_le_pow_iff_right (by grind)).mpr ?_
      have {a b : Nat} : a ≤ b → a.size ≤ b.size := by
        exact fun a_1 ↦ Nat.size_le_size a_1
      have hn' : 2 ≤ n := by exact hn
      have goal := this hn'
      exact goal
    refine Nat.sub_le_sub_right ?_ 1
    exact Nat.sub_le_sub_right this 1
  have t1 : 2 ^ n.size - 1 - 1 = 2 * (((2 ^ n.size - 1 - 1) / 2) - 1 + 1) := by
    have : 2 * (((2 ^ n.size - 1 - 1) / 2) - 1 + 1) = 2 * (((2 ^ n.size - 1 - 1) / 2)) := by
      refine mk_unique (2 * ((2 ^ n.size - 1 - 1) / 2 - 1 + 1)) (2 * ((2 ^ n.size - 1 - 1) / 2)) ?_
      have : (2 * ((2 ^ n.size - 1 - 1) / 2 - 1 + 1)) = (2 * ((2 ^ n.size - 1 - 1) / 2)) := by
        refine (Nat.mul_right_inj ?_).mpr (by grind)
        exact Ne.symm (Nat.zero_ne_add_one 1)
      simp [this] 
    have : (2 ^ n.size - 1 - 1) / 2 - 1 + 1 = (2 ^ n.size - 1 - 1) / 2 := by
      refine Nat.sub_add_cancel ?_
      have : (2 ^ (2 : Nat).size - 1 -1) / 2 ≤ (2 ^ n.size - 1 - 1) / 2 := by
        refine Nat.div_le_div_right ?_
        simp [s2]
        exact Nat.le_trans tr1 s3
      exact Nat.one_le_of_lt h
    simp [this]
    have : 2 * ((2 ^ n.size - 1 - 1) / 2) = 2 ^ n.size - 1 - 1 := by
      refine Nat.two_mul_div_two_of_even ?_
      simp [Even]
      use 2 ^ (n.size - 1) - 1
      have : 2 ^ (n.size - 1) - 1 + (2 ^ (n.size - 1) - 1) = 2 * 2 ^ (n.size - 1) - 1 - 1 := by
        have step1 : 2 ^ (n.size - 1) - 1 + (2 ^ (n.size - 1) - 1) =2 ^ (n.size - 1) - 1 + 2 ^ (n.size - 1) - 1 := by
          refine Eq.symm (Nat.add_sub_assoc ?_ (2 ^ (n.size - 1) - 1))
          have : 2 ^ ((2 : Nat).size - 1) ≤ 2 ^ (n.size - 1) := by
            refine Nat.pow_le_pow_right (by grind) ?_
            exact Nat.sub_le_sub_right le2 1
          simp [s2] at this
          exact Nat.one_le_two_pow
        simp [step1]
        grind
      simp [this]
      have : 2 * 2 ^ (n.size - 1) = 2 ^ n.size := by
        refine mul_pow_sub_one ?_ 2
        refine Nat.ne_zero_iff_zero_lt.mpr ?_
        refine Nat.size_pos.mpr ?_
        exact Nat.zero_lt_of_lt hn
      simp [this]
    simp [this]
  -- use h
  have : (2 ^ n.size - 1 - 1) / 2 - 1 + 1 = (2 ^ n.size - 1 - 1) / 2 := by
    refine Eq.symm (Nat.div_eq_of_eq_mul_right (by grind) t1)
  simp [this] at t1
  clear this
  have t2 : 2 * ((2 ^ n.size - 1 - 1) / 2) ≥ 2 * ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1) := by
    have t0 : (2 ^ n.size - 1 - 1) / 2 = 2 ^ (n.size - 1) - 1 := by  
      refine Nat.div_eq_of_eq_mul_right (by grind) ?_
      have : 2 * (2 ^(n.size - 1) - 1) = 2 * 2 ^ (n.size - 1) - 2 * 1 := by 
        exact Nat.mul_sub_left_distrib 2 (2 ^ (n.size - 1)) 1
      simp [this]
      clear this
      have : 2 * 2 ^ (n.size - 1) = 2 ^ 1 * 2 ^ (n.size - 1) := by exact rfl
      simp [this]
      clear this
      have : 2 ^ 1 * 2 ^ (n.size - 1) = 2 ^ n.size := by
        refine pow_mul_pow_sub 2 ?_
        have lt1 : 1 < (2 : Nat).size := by simp [s2]
        have le1 : 1 ≤ (2 : Nat).size := by exact Nat.one_le_of_lt lt1
        exact Nat.le_trans le1 le2
      have : 2 ^ 1 * 2 ^ (n.size - 1) - 2 = 2 ^ n.size - 2 := by 
        exact congrFun (congrArg HSub.hSub this) 2
      simp only [this]
      exact rfl
    simp only [t0]
    simp
    have mod (a b : Nat) (h : 0 < b) (h1 : a < b) : (a - 1) % b + 1 < b := by
      have mod1 (a b : Nat) (h : 0 < b) : (a - 1) % b < b := by
      apply?
      sorry
    simp [t0] at h 
    have h1 : 0 < 2 ^ (n.size - 1) - 1 := by exact Nat.zero_lt_of_lt h
    exact mod n (2 ^ (n.size - 1) - 1) h1 h
  have t0 : 2 ^ n.size - 1 = 2 * ((2 ^ n.size - 1 - 1) / 2 + 1) - 1 := by
    have : 2 * ((2 ^ n.size - 1 - 1) / 2 + 1) = (2 ^ n.size - 1 - 1) + 2 := by
      calc
        2 * ((2 ^ n.size - 1 - 1) / 2 + 1) = 2 * ((2 ^ n.size - 1 - 1) / 2) + 2 * 1 := by
          exact rfl
        _ = 2 * ((2 ^ n.size - 1 - 1) / 2) + 2 := by exact rfl  
        _ = (2 ^ n.size - 1 - 1) + 2 := by exact congrFun (congrArg HAdd.hAdd (id (Eq.symm t1))) 2
    simp only [this]
    have : 2 ^ n.size - 1 - 1 + 2 = 2 ^ n.size := by
      refine Eq.symm (Nat.eq_add_of_sub_eq ?_ rfl)
      have t1 : 2 ≤ 2 ^ (2 : Nat) := by exact Nat.succ_le_succ_sqrt' 1
      have t2 : 2 ^ (2 : Nat) ≤ 2 ^ n.size := by
        refine Nat.pow_le_pow_right (by grind) le2n
      exact Nat.le_trans t1 t2
    simp [this]
  -- exact Nat.lt_trans t2 t0
  rw [t0]
  sorry

theorem LubyTree.envelop_of_quotient_is_desceasing':
    ∀ n ≥ 2, ¬LubyTree.is_envelove n → LubyTree.enveloveSize n > LubyTree.enveloveSize (LubyTree.quotient n) := by
  intro n hn env
  simp [quotient, enveloveSize, enveloveDepth]
  -- simp [←length_of_bits_eq_size]
  have s1 {a b c : Nat} (h : a ≥ c) : a < b → a - c < b - c := by
    exact fun a_1 ↦ Nat.sub_lt_sub_right h a_1
  apply s1 
  {
    have : ∀ n : Nat, 2 ^ n ≥ 1 := by exact fun n ↦ Nat.one_le_two_pow
    exact this ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1).size
  }
  {
    have s1 {a b c : Nat} (h1 : 1 < a) : b < c → a ^ b < a ^ c := by
      refine (Nat.pow_lt_pow_iff_right h1).mpr
    apply s1 (by grind : 1 < 2)
    have s2 (a b : Nat) : 2 * a < b → a.size < b.size := by sorry
    apply s2
    sorry
    -- have (a b : Nat) (h : b > 0) : a % b < b := by exact Nat.mod_lt a h
    -- have t2 := this (n - 1)
  }
    --
  -- have : 2 ^ ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1).size < 2 ^ n.size →
  -- 2 ^ ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1).size - 1 < 2 ^ n.size - 1 := by apply?

def LubyTree.valueAtSize (self : LubyTree) (s : Nat) : Nat := match self with
  | .leaf     => 1
  | .wrap sub =>
    if self.size ≤ s then 2 ^ self.depth.pred else sub.valueAtSize ((s - 1) % sub.size + 1)

def LubyTree.luby (s : Nat) : Nat :=
  if h : LubyTree.is_envelove s
  then 2 ^ (LubyTree.enveloveDepth s).pred
  else
    have : s ≥ 2 := by
      by_contra h'
      have : s = 0 ∨ s = 1 := by grind
      have : is_envelove s = true := by
        simp [is_envelove, enveloveSize, enveloveDepth]
        rcases this with s01|s01 <;> simp [s01] 
      exact absurd this h
    have dec : s ≥ 2 → LubyTree.enveloveSize s > LubyTree.enveloveSize (LubyTree.quotient s) := by
     exact fun a ↦ envelop_of_quotient_is_desceasing' s this h
    LubyTree.luby (LubyTree.quotient s)
termination_by LubyTree.enveloveSize s

def LubyTree.valueAt (s : Nat) : Nat := (LubyTree.mk (s.succ.size - 1)).valueAtSize s

#eval! List.range 28 |>.map (fun n ↦ LubyTree.luby n.succ)
#eval List.range 28 |>.map (fun n ↦ LubyTree.valueAt n.succ)

theorem level_to_size (n : Nat) : (LubyTree.mk n).size = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp [LubyTree.mk, LubyTree.size]
  | succ n hn =>
    simp only [size_is_two_sub_sizes_add_one, hn]
    have : n + 1 + 1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one (n + 1))
    have : 2 ^ (n + 1 + 1) ≥ 2 := by exact Nat.le_self_pow this 2
    calc
      2 * (2 ^ (n + 1) - 1) + 1 = 2 * 2 ^ (n + 1) - 2 * 1 + 1 := by grind
      _ = 2 * 2 ^ (n + 1) - 2 + 1 := by omega
      _ = 2 ^ (n + 1 + 1) - 2 + 1 := by omega
      _ = 2 ^ (n + 1 + 1) + 1 - 2 := by omega
      _ = 2 ^ (n + 1 + 1) - 1 := by omega

theorem LubyTree.bit_patterns_of_top (t : LubyTree) : t.size.bits.all (· = true) := by
  induction t
  { simp [LubyTree.size] }
  {
    expose_names
    let n := tree.depth
    have hn : n = value_of% n := by rfl
    have : LubyTree.mk (n - 1) = tree := by
      simp [hn]
      exact LubyTree.mk_of_depth_eq_self tree
    simp -- [LubyTree.size]
    simp at tree_ih
    simp only [←this, size_is_two_sub_sizes_add_one' (n - 1)]
    simp only [Nat.bit1_bits]
    have notin_cons (a : Bool) (l : List Bool) : false ≠ a → false ∉ l → false ∉ a :: l := by 
      exact fun a_1 a_2 ↦ List.not_mem_cons_of_ne_of_not_mem a_1 a_2
    apply notin_cons
    { simp }
    { simp [this] ; exact tree_ih }
  }

theorem LubyTree.is_symmetry (d : Nat) :
    ∀ n ≤ ((LubyTree.mk d).size - 1) / 2,
      n > 0 → (LubyTree.mk d).valueAtSize n = (LubyTree.mk d).valueAtSize (n + ((LubyTree.mk d).size - 1) / 2)  := by
  intro n hn nz
  induction' d with d dh
  { 
    simp [LubyTree.mk]
    simp [LubyTree.size]
  }
  {
    rw [LubyTree.valueAtSize.eq_def]
    rw [LubyTree.valueAtSize.eq_def]
    split
    { rfl } -- case: leaf
    {
      -- case: wrap sub
      expose_names
      have d_tree : mk d = tree := by exact (unwrap_wrap_self_eq_self d tree).mp heq
      simp [←d_tree] at *
      -- simp [heq] at *
      have d_eq : (mk (d + 1)).depth = (mk d).depth + 1 := by exact rfl
      simp only [d_eq] at * 
      split
      {
        split
        { expose_names ; exact rfl }
        {
          expose_names
          have : ¬(mk (d + 1)).size ≤ n := by grind
          exact absurd h this
        }
      } 
      {
        split
        { expose_names ; grind }
        {
          expose_names
          have : (n - 1) % (mk d).size = (n + ((mk (d + 1)).size - 1) / 2 - 1) % (mk d).size := by
            have : (mk (d + 1)).size = 2 * (mk d).size + 1 := by exact size_is_two_sub_sizes_add_one d
            simp [this]
            rw [add_comm]
            -- have (m a : Nat) : (m + a) % m = a % m := by apply? -- exact Nat.sub_add_comm h
            rw [←Nat.add_mod_left (mk d).size (n - 1)] 
            have : (mk d).size + (n - 1) = (mk d).size + n - 1 := by
              exact Eq.symm (Nat.add_sub_assoc nz (mk d).size)
            rw [this]
          simp [this]
       }
     }
   }
 }

end Tree

