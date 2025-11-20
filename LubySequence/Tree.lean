module

import Mathlib.Tactic
public import LubySequence.Size
public import LubySequence.Utils

namespace Tree

/-
 - The level of LubyTrees starts with 1.
 - The index of the elements of LubyTree starts with 0.
 -/

public inductive LubyTree where
  | leaf : LubyTree
  | wrap (tree : LubyTree) : LubyTree
deriving BEq

@[expose]
public def LubyTree.mk (level : ℕ) : LubyTree := match level with
  | 0     => LubyTree.leaf
  | l + 1 => wrap (LubyTree.mk l)

def LubyTree.toString (self : LubyTree) : String := match self with
  | .leaf => "leaf"
  | wrap (tree : LubyTree) => s!"↑{tree.toString}"

instance : ToString LubyTree where
  toString := LubyTree.toString

def t4 := LubyTree.mk 4
-- #eval t4 -- LubyTree.mk 4

theorem LubyTree.wrap_is_congruent (t1 t2 : LubyTree) : t1.wrap = t2.wrap ↔ t1 = t2 := by
  constructor
  { intro h ; simp at h ; exact h }
  { intro h ; simp ; exact h }

def LubyTree.depth (self : LubyTree) : ℕ := match self with
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
    { expose_names
      have this := LubyTree.depth_gt_one sub
      have : ¬sub.depth = 0 := by exact Nat.ne_zero_of_lt this
      exact absurd heq this }
    { expose_names
      have : sub.depth - 1 = l.succ - 1 := by exact congrFun (congrArg HSub.hSub heq) 1
      have : sub.depth - 1 = l := by exact this
      simp [←this, tree_ih] }

-- #eval LubyTree.mk 0
-- #eval LubyTree.leaf.depth

theorem LubyTree.mk_self_eq_depth_add_one (n: ℕ) : (LubyTree.mk n).depth = n + 1 := by
  induction n with
  | zero =>
    simp [LubyTree.mk]
    rfl
  | succ n ih =>
    simp [LubyTree.mk]
    simp [LubyTree.depth]
    exact ih

theorem LubyTree.mk_zero_is_leaf {n : ℕ} : LubyTree.mk n = LubyTree.leaf → n = 0 := by
  induction n with
  | zero => intro h ; simp [mk] at h ; exact rfl
  | succ n hn => intro h ; simp [mk] at h

theorem LubyTree.wrap_n_eq_n_add_one (n : ℕ) : LubyTree.wrap (LubyTree.mk n) = LubyTree.mk (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [←ih]
    rewrite (occs := .pos [2]) [LubyTree.mk.eq_def]
    split
    { expose_names
      have (n : ℕ) : n + 1 ≠ 0 := by exact Ne.symm (Nat.zero_ne_add_one n)
      have hne := this (n + 1)
      exact absurd heq hne }
    { expose_names
      have : n + 1 = l := by exact Nat.succ_inj.mp heq
      rw [←this]
      simp [ih] }

theorem LubyTree.mk_unique (m n : ℕ) : LubyTree.mk m = LubyTree.mk n → m = n := by
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
    { have : n = (n - 1) + 1 := by exact Eq.symm (Nat.succ_pred_eq_of_ne_zero f)
      rw [this] at h
      rw [←LubyTree.wrap_n_eq_n_add_one] at h
      rw [←LubyTree.wrap_n_eq_n_add_one] at h
      have : mk m = mk (n - 1) := by
        exact (wrap_is_congruent (mk m) (mk (n - 1))).mp h
      have h' := hm (n - 1) this
      grind }

theorem LubyTree.unwrap_wrap_self_eq_self (d : ℕ) (t : LubyTree) :
    LubyTree.mk (d + 1) = t.wrap ↔ LubyTree.mk d = t := by
  constructor
  { intro h ; simp [LubyTree.mk] at h ; exact h }
  { intro h ; simp [LubyTree.mk] ; exact h }

def LubyTree.size (self : LubyTree) : ℕ := match self with
  | .leaf => 1
  | wrap tree => tree.size * 2 + 1

-- #eval List.range 5 |>.map (fun n ↦ (LubyTree.mk n).size)

theorem LubyTree.size_ge_one (t : LubyTree) : t.size ≥ 1 := by
  induction t <;> simp [LubyTree.size]

theorem size_is_two_sub_sizes_add_one (n : ℕ) :
    (LubyTree.mk (n + 1)).size = 2 * (LubyTree.mk n).size + 1 := by
  rw [LubyTree.mk, LubyTree.size]
  grind

theorem size_is_two_sub_sizes_add_one' (n : ℕ) :
    (LubyTree.mk n).wrap.size = 2 * (LubyTree.mk n).size + 1 := by
  simp [←size_is_two_sub_sizes_add_one]
  exact rfl

-- #eval Nat.bits (2 * 5)

theorem depth_and_size (tree : LubyTree) : tree.depth = tree.size.size := by
  induction tree
  { simp [LubyTree.depth, LubyTree.size] }
  { expose_names
    simp [LubyTree.depth]
    simp [LubyTree.size]
    simp [tree_ih]
    simp [←bitslength_eq_size, Nat.mul_comm tree.size 2] }

/-
 - The envelope is the smallest tree containing `s` elements.
 -/
@[expose]
public def LubyTree.envelopeDepth (s : ℕ) : ℕ := s.size

@[expose]
public def LubyTree.envelopeSize (s : ℕ) : ℕ := 2 ^ (LubyTree.envelopeDepth s) - 1

@[expose]
public def LubyTree.envelope (s : ℕ) : LubyTree := LubyTree.mk (LubyTree.envelopeDepth s - 1)

@[expose]
public def LubyTree.is_envelope (s : ℕ) : Bool := LubyTree.envelopeSize s = s

def LubyTree.quotientOfSize (s : ℕ) (e : ℕ) := (s - 1) % ((e - 1) / 2) + 1

@[expose]
public def LubyTree.quotient (s : ℕ) := (s - 1) % (((2 ^ s.size - 1) - 1) / 2) + 1

-- #eval List.range 20 |>.map (fun n ↦ (n + 1, LubyTree.envelopeDepth (n + 1)))
-- #eval List.range 20 |>.map (fun n ↦ (n + 1, LubyTree.envelopeSize (n + 1), LubyTree.is_envelope (n + 1)))
-- #eval LubyTree.quotientOfSize 2 3
-- #eval LubyTree.is_envelope 2
-- #eval LubyTree.envelopeSize 2
-- #eval LubyTree.is_envelope 1
-- #eval LubyTree.is_envelope 0

-- This is impossible
-- theorem LubyTree.quotient_is_decreasing : ∀ n ≥ 2, n > LubyTree.quotient n := by

theorem LubyTree.envelop_of_quotient_is_decreasing :
    ∀ n ≥ 2, n < (2 ^ n.size - 1 - 1) / 2 → LubyTree.envelopeSize n > 2 * (LubyTree.quotient n) := by
  intro n hn h
  simp only [LubyTree.quotient, LubyTree.envelopeSize, LubyTree.envelopeDepth]
  have s2 : Nat.size 2 = 2 := by simp [Nat.size, Nat.binaryRec]
  have le2 : (2 : ℕ).size ≤ n.size := by exact Nat.size_le_size hn
  have le2' : 2 ≤ (2 : ℕ).size := by exact Nat.le_of_eq (id (Eq.symm s2))
  have le2n : 2 ≤ n.size := by exact Nat.le_trans le2' le2
  have le2p : 4 ≤ 2 ^ n.size := by
    have : 2 ^ 2 ≤ 2 ^ n.size := by refine Nat.pow_le_pow_right (by grind) le2n
    exact this
  have tr1 : 2 ≤ 2 ^ (2 : ℕ).size - 1 - 1 := by
    have : (2 : ℕ).size = 2 := by simp [Nat.size, Nat.binaryRec]
    simp [this]
  have s3 : 2 ^ (2 : ℕ).size - 1 - 1 ≤ 2 ^ n.size - 1 - 1 := by
    have : 2 ^ (2 : ℕ).size ≤ 2 ^ n.size := by
      refine (Nat.pow_le_pow_iff_right (by grind)).mpr ?_
      have {a b : ℕ} : a ≤ b → a.size ≤ b.size := by
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
      have : (2 ^ (2 : ℕ).size - 1 -1) / 2 ≤ (2 ^ n.size - 1 - 1) / 2 := by
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
          have : 2 ^ ((2 : ℕ).size - 1) ≤ 2 ^ (n.size - 1) := by
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
  have : (2 ^ n.size - 1 - 1) / 2 - 1 + 1 = (2 ^ n.size - 1 - 1) / 2 := by
    refine Eq.symm (Nat.div_eq_of_eq_mul_right (by grind) t1)
  simp [this] at t1
  clear this
  have t1' : 2 ^ n.size - 1 = 2 * ((2 ^ n.size - 1 - 1) / 2) + 1 := by
    have c1 : 2 ^ n.size - 1 - 1 + 1 = 2 * ((2 ^ n.size - 1 - 1) / 2) + 1 := by
      exact congrFun (congrArg HAdd.hAdd t1) 1
    have c2 : 2 ^ n.size - 1 - 1 + 1 = 2 ^ n.size - 1 := by
      refine Nat.sub_add_cancel ?_
      have : 1 + 1 ≤ 2 ^ n.size := by exact Nat.le_of_add_left_le le2p
      exact Nat.le_sub_one_of_lt this
    rw [←c2]
    exact c1
  have t2 : 2 * ((2 ^ n.size - 1 - 1) / 2) ≥ 2 * ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1) := by
    have c1 : (n - 1) % ((2 ^ n.size - 1 - 1) / 2) < (2 ^ n.size - 1 - 1) / 2 := by
      refine mod_gt_right (n - 1) ((2 ^ n.size - 1 - 1) / 2) ?_
      grind
    have c2 : (n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1 ≤ (2 ^ n.size - 1 - 1) / 2 := by exact c1
    have c3 : 2 * ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1) ≤ 2 * ((2 ^ n.size - 1 - 1) / 2) := by
      exact Nat.mul_le_mul_left 2 c1
    clear c2
    exact c3
  have t2' : 2 * ((2 ^ n.size - 1 - 1) / 2) + 1 > 2 * ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1) := by
    exact Order.lt_add_one_iff.mpr t2
  have t0 : 2 ^ n.size - 1 = 2 * ((2 ^ n.size - 1 - 1) / 2) + 1 := by
    have : 2 * ((2 ^ n.size - 1 - 1) / 2) = (2 ^ n.size - 1 - 1) := by exact id (Eq.symm t1)
    simp only [this]
    have : 2 ^ n.size - 1 - 1 + 2 = 2 ^ n.size := by
      refine Eq.symm (Nat.eq_add_of_sub_eq ?_ rfl)
      have t1 : 2 ≤ 2 ^ (2 : ℕ) := by exact Nat.succ_le_succ_sqrt' 1
      have t2 : 2 ^ (2 : ℕ) ≤ 2 ^ n.size := by
        refine Nat.pow_le_pow_right (by grind) le2n
      exact Nat.le_trans t1 t2
    simp [this]
  -- exact Nat.lt_trans t2 t0
  nth_rewrite 1 [t0]
  clear t0
  exact t2'

-- #eval List.range 28 |>.map (· + 2) |>.map (fun n ↦ (n, LubyTree.is_envelope n, LubyTree.envelopeSize n, LubyTree.envelopeSize (LubyTree.quotient n)))

-- #eval List.range 28 |>.map (· + 2) |>.map (fun n ↦ (2 * ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1), ((2 ^ n.size - 1 - 1) / 2), n))

theorem LubyTree.envelop_of_quotient_is_decreasing':
    ∀ n ≥ 2, ¬LubyTree.is_envelope n → LubyTree.envelopeSize n > LubyTree.envelopeSize (LubyTree.quotient n) := by
  intro n hn env
  -- basic facts
  have es2 : Nat.size 2 = 2 := by simp [Nat.size, Nat.binaryRec]
  have le2 : (2 : ℕ).size ≤ n.size := by exact Nat.size_le_size hn
  have le2' : 2 ≤ (2 : ℕ).size := by exact Nat.le_of_eq (id (Eq.symm es2))
  have le2n : 2 ≤ n.size := by exact Nat.le_trans le2' le2
  have le2p : 4 ≤ 2 ^ n.size := by
    have : 2 ^ 2 ≤ 2 ^ n.size := by refine Nat.pow_le_pow_right (by grind) le2n
    exact this
  have le2p' : 4 ≤ 2 ^ n.bits.length := by
    simp [bitslength_eq_size]
    exact le2p
  have le2nbl : 2 ≤ n.bits.length := by
    have step1 : (2 : ℕ).bits.length ≤ n.bits.length := by exact bitslength_le_bitslength hn
    have step2 : (2 : ℕ).bits.length = 2 := by
      calc
        (2 : ℕ).bits.length = [false, true].length := by
          have : (2 : ℕ).bits = [false, true] := by simp [Nat.bits, Nat.binaryRec]
          simp [this]
        _ = 2 := by exact rfl
    simp [step2] at step1
    exact step1
  simp [envelopeSize, envelopeDepth]
  have s1 : 2 ^ (quotient n).size < 2 ^ n.size → 2 ^ (quotient n).size - 1 < 2 ^ n.size - 1 := by
    have (a b : ℕ) (h : 1 ≤ a) : a < b → a - 1 < b - 1 := by
      exact fun a_1 ↦ Nat.sub_lt_sub_right h a_1
    have h0 : 1 ≤ 2 ^ (quotient n).size := by exact Nat.one_le_two_pow
    exact fun a ↦ this (2 ^ (quotient n).size) (2 ^ n.size) h0 a
  apply s1
  clear s1
  simp [quotient]
  have s2 (a b c : ℕ) (h : 1 < c) : a < b ↔ c ^ a < c ^ b := by
    exact Iff.symm (Nat.pow_lt_pow_iff_right h)
  apply (s2 ((n - 1) % ((2 ^ n.size - 1 - 1) / 2) + 1).size n.size 2 (by grind)).mp
  clear s2
  -- size_lt で条件が緩くなりすぎる
  -- refine size_lt (by grind) ?_
  -- やり直し
  simp [←bitslength_eq_size]
  -- - 1 - 1 を削除して % を削除して + 1 を削除して
  -- (2 ^ (n.bits.length - 1)).bits.length < n.bits.length の形に持ち込みたい。
  have s1 : (2 ^ n.bits.length - 1 - 1).bits.length = n.bits.length := by
    have tmp : (2 ^ n.bits.length - 1 - 1).bits.length = (2 ^ n.bits.length - 2).bits.length := by
      have : 2 ^ n.bits.length - 1 - 1 = 2 ^ n.bits.length - 2 := by exact rfl
      exact rfl
    simp [tmp]
    clear tmp
    simp [bitslength_eq_size]
    refine size_sub ?_ ?_ ?_
    · exact Nat.zero_lt_of_lt le2n
    · exact Nat.two_pos
    · exact Nat.le_self_pow (Nat.sub_ne_zero_iff_lt.mpr le2n) 2
  have s1' : ((2 ^ n.bits.length - 1 - 1) / 2).bits.length = n.bits.length - 1 := by
    have t1 {x : ℕ} (h : 2 ≤ x) : (x / 2).bits = x.bits.tail := by
      let v := (x / 2).bits
      have vp : v = value_of% v := by exact rfl
      have tf : x % 2 = 0 ∨ ¬ x % 2 = 0 := by exact eq_or_ne _ _
      rcases tf with t|f
      { have s1 : Even x := by refine Nat.even_iff.mpr t
        have s2 : x = 2 * (x / 2) := by refine Eq.symm (Nat.two_mul_div_two_of_even s1)
        have s3 : x.bits = (2 * (x / 2)).bits := by exact congrArg Nat.bits s2
        have s4 : (2 * (x / 2)).bits = false :: (x / 2).bits := by
          refine Nat.bit0_bits (x / 2) ?_
          have t1 : 0 < 2 / 2 := by grind
          have t2 : 2 / 2 ≤ x / 2 := by exact Nat.div_le_div_right h
          have t3 : 0 < x / 2 := by exact t2
          have t4 : x / 2 ≠ 0 := by exact Nat.ne_zero_of_lt t2
          exact t4
        simp [←s2] at s4
        have s4' : x.bits.tail = (false :: (x / 2).bits).tail := by exact congrArg List.tail s4
        have s5 : (false :: (x / 2).bits).tail = (x /2).bits := by exact vp
        simp [←s4'] at s5
        exact id (Eq.symm s4') }
      { have : x % 2 = 1 := by exact Nat.mod_two_ne_zero.mp f
        have s1 : ¬ Even x := by exact Nat.not_even_iff.mpr this
        have s1' : Odd x := by exact Nat.odd_iff.mpr this
        have s2 : x = 2 * (x / 2) + 1 := by exact Eq.symm (Nat.two_mul_div_two_add_one_of_odd s1')
        have s3 : x.bits = (2 * (x / 2) + 1).bits := by exact congrArg Nat.bits s2
        have s4 : (2 * (x / 2) + 1).bits = true :: (x / 2).bits := by exact Nat.bit1_bits (x / 2)
        simp [←s2] at s4
        have s4' : x.bits.tail = (true :: (x / 2).bits).tail := by exact congrArg List.tail s4
        exact id (Eq.symm s4') }
    have t2 : 2 ≤ 2 ^ n.bits.length - 1 - 1 := by grind
    have t1' := t1 t2
    clear t1 t2
    have t1'' : ((2 ^ n.bits.length - 1 - 1) / 2).bits.length = (2 ^ n.bits.length - 1 - 1).bits.tail.length := by
      exact congrArg List.length t1'
    clear t1'
    simp [t1'']
    clear t1''
    simp [s1]
  have s2 : ((n - 1) % ((2 ^ n.bits.length - 1 - 1) / 2) + 1) ≤ ((2 ^ n.bits.length - 1 - 1) / 2) := by
    refine mod_gt_right'' ?_ ?_
    have tmp : 0 < (2 ^ n.bits.length - 1 - 1) / 2 := by
      have : 0 < 2 ^ n.bits.length - 1 - 1 := by
        have : 2 ^ 2 ≤ 2 ^ n.bits.length := by refine Nat.pow_le_pow_right (by grind) le2nbl
        have : 2 ^ 2 - 1 ≤ 2 ^ n.bits.length - 1 := by exact Nat.sub_le_sub_right this 1
        simp at this
        have : 3 - 1 ≤ 2 ^ n.bits.length - 1 - 1 := by exact Nat.sub_le_sub_right this 1
        simp at this
        exact Nat.zero_lt_of_lt this
      have : 0 < (2 ^ n.bits.length - 1 - 1) / 2 := by
        refine Nat.div_pos ?_ (by grind)
        { have : 4 - 1 ≤ 2 ^ n.bits.length - 1 := by exact Nat.sub_le_sub_right le2p' 1
          have : 4 - 1 - 1 ≤ 2 ^ n.bits.length - 1 - 1 := by exact Nat.sub_le_sub_right this 1
          simp at this
          exact this }
      exact this
    exact tmp
  have s2' : ((n - 1) % ((2 ^ n.bits.length - 1 - 1) / 2) + 1).bits.length ≤ ((2 ^ n.bits.length - 1 - 1) / 2).bits.length := by
    exact bitslength_le_bitslength s2
  clear s2

  have r1 : (n - 1) % ((2 ^ n.bits.length - 1 - 1) / 2) + 1 ≤ (2 ^ n.bits.length - 1 - 1) / 2 := by
    refine mod_gt_right'' n ?_
    { have : 4 - 1 ≤ 2 ^ n.bits.length - 1 := by exact Nat.sub_le_sub_right le2p' 1
      simp at this
      have : 3 - 1 ≤ 2 ^ n.bits.length - 1 - 1 := by exact Nat.sub_le_sub_right this 1
      simp at this
      have : 2 / 2 ≤ (2 ^ n.bits.length - 1 - 1) / 2 := by exact Nat.div_le_div_right this
      simp at this
      exact this }
  have r2 : (2 ^ n.bits.length - 1 - 1) / 2 < n := by
    have : (2 ^ n.bits.length - 1 - 1) / 2 = 2 ^ n.bits.length / 2 - 1 := by
      calc
        (2 ^ n.bits.length - 1 - 1) / 2 = (2 ^ n.bits.length - 2) / 2 := by exact rfl
        _ = 2 ^ n.bits.length / 2 - 2 / 2 := by
          refine Nat.div_eq_of_eq_mul_right (by grind) ?_
          simp [Nat.mul_sub]
          have : 2 * (2 ^ n.bits.length / 2) = 2 ^ n.bits.length := by
            refine Nat.mul_div_cancel' ?_
            refine Dvd.dvd.pow (by grind) (by grind)
          simp [this]
        _ = 2 ^ n.bits.length / 2 - 1 := by exact rfl
    simp [this]
    have : 2 ^ n.size ≤ 2 * n := by exact pow_two_of_size_le_self (by grind)
    have : 2 ^ n.bits.length ≤ 2 * n := by
      rw [bitslength_eq_size]
      exact this
    have : 2 ^ n.bits.length / 2 ≤ n := by exact Nat.div_le_of_le_mul this
    have tr1 : 2 ^ n.bits.length / 2 - 1 ≤ n - 1 := by exact Nat.sub_le_sub_right this 1
    have tr2 : n - 1 < n := by exact Nat.sub_one_lt_of_lt hn
    exact Nat.lt_of_le_of_lt tr1 tr2
  simp [s1'] at s2'
  have : n.bits.length - 1 < n.bits.length := by exact Nat.sub_one_lt_of_lt le2nbl
  exact Nat.lt_of_le_of_lt s2' this

def LubyTree.valueAtSize (self : LubyTree) (s : ℕ) : ℕ := match self with
  | .leaf     => 1
  | .wrap sub =>
    if self.size ≤ s then 2 ^ self.depth.pred else sub.valueAtSize ((s - 1) % sub.size + 1)

@[expose]
public def LubyTree.luby (s : ℕ) : ℕ :=
  if h : LubyTree.is_envelope s
  then 2 ^ (LubyTree.envelopeDepth s).pred
  else
    have : s ≥ 2 := by
      by_contra h'
      have : s = 0 ∨ s = 1 := by grind
      have : is_envelope s = true := by
        simp [is_envelope, envelopeSize, envelopeDepth]
        rcases this with s01|s01 <;> simp [s01]
      exact absurd this h
    have dec : s ≥ 2 → LubyTree.envelopeSize s > LubyTree.envelopeSize (LubyTree.quotient s) := by
     exact fun a ↦ envelop_of_quotient_is_decreasing' s this h
    LubyTree.luby (LubyTree.quotient s)
termination_by LubyTree.envelopeSize s

public def LubyTree.valueAt (s : ℕ) : ℕ := (LubyTree.mk (s.succ.size - 1)).valueAtSize s

-- #eval! List.range 28 |>.map (fun n ↦ LubyTree.luby n.succ)
-- #eval List.range 28 |>.map (fun n ↦ LubyTree.valueAt n.succ)

theorem level_to_size (n : ℕ) : (LubyTree.mk n).size = 2 ^ (n + 1) - 1 := by
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
  { expose_names
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
    { simp [this] ; exact tree_ih } }

theorem LubyTree.is_symmetry (d : ℕ) :
    ∀ n ≤ ((LubyTree.mk d).size - 1) / 2,
      n > 0 → (LubyTree.mk d).valueAtSize n = (LubyTree.mk d).valueAtSize (n + ((LubyTree.mk d).size - 1) / 2) := by
  intro n hn nz
  induction d with
  | zero => simp [LubyTree.mk, LubyTree.size]
  | succ d dh =>
    rw [LubyTree.valueAtSize.eq_def]
    rw [LubyTree.valueAtSize.eq_def]
    split
    { rfl } -- case: leaf
    { -- case: wrap sub
      expose_names
      have d_tree : mk d = tree := by exact (unwrap_wrap_self_eq_self d tree).mp heq
      simp [←d_tree] at *
      -- simp [heq] at *
      have d_eq : (mk (d + 1)).depth = (mk d).depth + 1 := by exact rfl
      simp only [d_eq] at *
      split
      { split
        { expose_names ; exact rfl }
        { expose_names
          have : ¬(mk (d + 1)).size ≤ n := by grind
          exact absurd h this } }
      { split
        { expose_names ; grind }
        { expose_names
          have : (n - 1) % (mk d).size = (n + ((mk (d + 1)).size - 1) / 2 - 1) % (mk d).size := by
            have : (mk (d + 1)).size = 2 * (mk d).size + 1 := by exact size_is_two_sub_sizes_add_one d
            simp [this]
            rw [add_comm]
            -- have (m a : ℕ) : (m + a) % m = a % m := by apply? -- exact Nat.sub_add_comm h
            rw [←Nat.add_mod_left (mk d).size (n - 1)]
            have : (mk d).size + (n - 1) = (mk d).size + n - 1 := by
              exact Eq.symm (Nat.add_sub_assoc nz (mk d).size)
            rw [this]
          simp [this] } } }

end Tree
