import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Size
import Utils

namespace Luby

/-
  The Luby sequence is a sequence of natural numbers defined recursively.
  It is used in randomized algorithms and has applications in computer science.
  The sequence is defined as follows:

  L(k ≥ 1) = 2^(i-1)          if k = 2^i - 1 for some i ≥ 0,
           = L(k+1 - 2^(i-1)) if 2^(i-1) ≤ k ≤ 2^i - 1

If we want to start the sequence from 0, to make the mapping a total function:

  L(k ≥ 0) = 2^(i-1)          if k = 2^i - 2 for some i ≥ 0,
           = L(k+2 - 2^(i-1)) if 2^(i-1) ≤ k + 1 ≤ 2^i - 1

Or

  L(k ≥ 0) = 2^(I(k)-1)          if (k + 2) &&& (k + 1) = 0,
           = L(k+2 - 2^(I(k)-1)) otherwise
where
  I(n) = ⌈log₂(n+2)⌉
-/

/--
 - Basic relation between Nat and its binary representation.
 - A kind of ceiling function.
 -
 - This is the envelopeMax (zero-based indexed)
 -/
def S₂ (n : Nat) := 2 ^ (n.succ.size - 1)
#eval List.range 24 |>.map S₂

theorem pow2_le_pow2 (a b : Nat) : a ≤ b → 2 ^ a ≤ 2 ^ b := by
  exact Nat.pow_le_pow_right (by grind : 2 > 0)

theorem S₂_ge_zero (n : Nat) : S₂ n ≥ 0 := by
  simp [S₂]

theorem S₂_is_mono : ∀ n ≥ 0, S₂ n ≤ S₂ (n + 1) := by
  intro i n0
  induction' i with a h
  { simp [S₂, Nat.size, Nat.binaryRec] }
  {
    simp at h
    dsimp [S₂, Nat.size]
    apply pow2_le_pow2
    rw [←Nat.size]
    apply fun x ↦ Nat.sub_le_sub_right x 1
    apply Nat.size_le_size
    grind
  }

theorem S₂_ge_two (k : Nat) (h : k > 0) : S₂ k ≥ 2 := by
  simp [S₂]
  rw [(by rfl : 2 = 2 ^1)]
  apply pow2_le_pow2
  apply Nat.le_sub_of_add_le
  simp
  have : 2 ≤ (k + 1).size := by
    have h1 : k = 1 ∨ k > 1 := by exact LE.le.eq_or_gt h
    rcases h1 with h1|h2
    { simp [h1, Nat.size, Nat.binaryRec] }
    {
      have h1 : 1 = (1 : Nat).size := by exact Eq.symm Nat.size_one
      have h2 : 2 ≤ (2 : Nat).size := by simp [Nat.size, Nat.binaryRec]
      have h3 : 2 ≤ 1 + k := by grind
      have h4 : Nat.size 2 ≤ Nat.size (k + 1) := by
        simp only [Nat.add_comm k 1]
        exact Nat.size_le_size h3
      exact Nat.le_trans h2 h4
    }
  exact this

theorem power2_ge_linear (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction' n with k h
  { simp }
  {
    have h2 : 2 ^(k + 1) = 2^k * 2 := by omega
    rw [h2]
    have t1 : k + 1 + 1 ≤ 2 ^ k + 1 := by omega
    have t2 : 2 ^ k + 1 ≤ 2 ^ k + 2 ^ k := by
      have : 1 ≤ 2 ^ k := by omega
      exact Nat.add_le_add_iff_left.mpr this
    have (k : Nat) : k + k = k * 2 := by exact Eq.symm (Nat.mul_two k)
    rw [this] at t2
    exact Nat.le_trans t1 t2
  }

#eval List.range 24 |>.map (fun k ↦ S₂ k == k)
#eval List.range 24 |>.map (fun k ↦ S₂ (k + 2) == k + 2)

def is_envelope (n : Nat) : Bool := S₂ (n + 2) = n + 2

-- Well-founded version of the Luby sequence
def luby (n : ℕ) : Nat := if is_envelope n then S₂ n else luby (n + 1 - S₂ n)
termination_by n
decreasing_by
  rcases n with z | k
  {
    expose_names
    simp [is_envelope] at h
    simp at *
    have : S₂ 2 = 2 := by simp [S₂, Nat.size, Nat.binaryRec]
    exact absurd this h
  }
  {
    expose_names
    ring_nf at *
    simp at *
    have : 2 - S₂ (1 + k) < 1 → 2 + k - S₂ (1 + k) < 1 + k := by omega
    apply this
    have : 1 < S₂ (1 + k) → 2 - S₂ (1 + k) < 1 := by
      intro h
      have : S₂ (1 + k) ≥ 2 := by exact S₂_ge_two (1 + k) (by grind)
      grind
    apply this
    apply S₂_ge_two (1 + k) (by grind)
  }

#eval S₂ 0 -- 2 = 2 -- 0
#eval luby 2 -- 2 = 2 -- 0

/-
theorem Luby_value_is_double_or_one : ∀ n : Nat, luby (n + 1) = 2 * luby n ∨ luby (n + 1) = 1 := by
  sorry
-/

def is_segment_beg (n : Nat) : Bool := match h : n with 
  | 0 => true
  | 1 => true
  | m + 1 + 1 => if is_envelope n then false else is_segment_beg (n + 1 - S₂ n)
termination_by n
decreasing_by
  expose_names
  have decreasing : n + 1 - S₂ n < n := by
    simp [S₂]
    have t1 : n = m + 2 := by exact h
    have t2 : 0 ≤ m := by exact Nat.zero_le m
    have t2' : 2 ≤ m + 2 := by exact Nat.le_add_of_sub_le t2
    simp [←t1] at t2'
    have goal : 1 < S₂ n := by
      simp [S₂]
      have s1 : (2 + 1).size ≤ (n + 1).size := by
        refine Nat.size_le_size ?_
        exact Nat.add_le_add_right t2' 1
      have s2 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
      simp [s2] at s1
      exact Nat.sub_ne_zero_iff_lt.mpr s1
    simp only [S₂] at goal
    have : n.succ = n + 1 := by rfl
    simp only [this] at goal
    have goal1 : n + 1 < n + 2 ^ ((n + 1).size - 1) := by exact Nat.add_lt_add_left goal n
    have goal2 : n + 1 - 2 ^ ((n + 1).size - 1) < n := by 
      have (a b c : Nat) (h : a ≥ c) : a < b + c → a - c < b := by
        exact Nat.sub_lt_right_of_lt_add h 
      have c : n + 1 ≥ 2 ^ ((n + 1).size - 1) := by
        refine n_ge_subenvelope ?_
        exact Nat.le_add_left 1 n
      exact this (n + 1) n (2 ^ ((n + 1).size - 1)) c goal1
    exact goal2
  simp only [←h]
  exact decreasing

#eval! is_segment_beg 7 -- false
#eval! is_envelope 0 -- false

theorem luby_value_at_segment_beg (n : Nat) : is_segment_beg n → luby n = 1 := by
  have luby0 : luby 0 = 1 := by
    rw [luby]
    simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
  have luby1 : luby 1 = 1 := by
    rw [luby]
    simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
    exact luby0
  induction' n using Nat.strong_induction_on with n nh
  { expose_names
    intro h
    rw [is_segment_beg.eq_def] at h
    split at h
    { expose_names ; exact luby0 }
    { expose_names ; simp [luby1] }
    { expose_names
      split at h
      { contradiction }
      { expose_names
        rw [luby]
        split
        { expose_names ; exact absurd h_2 h_1 }
        { expose_names
          simp at *
          let n := m + 1 + 1
          have np : n = value_of% n := by exact rfl
          simp [←np] at *
          simp [S₂]
          have r : n + 1 - 2 ^ ((n + 1).size - 1) < n := by 
            have (a b c : Nat) (h : a ≥ c) : a < b + c → a - c < b := by
              exact Nat.sub_lt_right_of_lt_add h 
            have c : n + 1 ≥ 2 ^ ((n + 1).size - 1) := by
              refine n_ge_subenvelope ?_
              exact Nat.le_add_left 1 n
            refine this (n + 1) n (2 ^ ((n + 1).size - 1)) c ?_
            have : 1 < 2 ^ ((n + 1).size - 1) := by
              have n2 : n ≥ 2 := by exact Nat.le_add_left 2 m
              have t1 : (2 + 1).size ≤ (n + 1).size := by
                refine Nat.size_le_size ?_
                exact Nat.add_le_add_right n2 1
              have t2 : (2 + 1).size = 2 := by simp [Nat.size, Nat.binaryRec]
              simp [t2] at t1
              have t3 : 1 ≤ (n + 1).size - 1 := by exact Nat.le_sub_one_of_lt t1
              have t4 : 2 ≤ 2 ^ ((n + 1).size - 1) := by exact Nat.le_pow t3
              exact t4
            exact Nat.add_lt_add_left this n
          have goal := nh (n + 1 - S₂ n) r h
          exact goal
        } 
      }
    }
  }

#eval (is_envelope 14, (14 + 2).size == (14 + 1).size + 1)

-- これは 2 ^ n - (2 ^ n - 1) = 1 以外の元を取ると距離が1を超えてしまうことから背理法で言える
theorem envelope_prop1 (n : Nat) : n + 2 = 2 ^ ((n + 2).size - 1) ↔ is_envelope n := by
  constructor
  { intro h
    simp [is_envelope, S₂]
    nth_rw 2 [h]
    have (a b : Nat) : a = b → 2 ^ a = 2 ^ b := by exact fun a_1 ↦ congrArg (HPow.hPow 2) a_1
    apply this
    
    sorry
  }

theorem envelope_prop2 (n : Nat) : (n + 2).size = (n + 1).size + 1 ↔ is_envelope n := by
  constructor
  {
    intro h
    simp [is_envelope, S₂]
    have t1 : 2 ^ ((n + 2 + 1).size - 1) = (n + 2 + 1).size - 1 + 1 := by
      apply?

    have t1 : (n + 2).size - 1 = (n + 1).size := by 
      exact Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm h)))
    clear h



    sorry
  }
  sorry

theorem luby_value_not_at_segment_beg (n : Nat) :
    ¬is_segment_beg (n + 1) → luby (n + 1) = 2 * luby n := by
  intro h
  have luby0 : luby 0 = 1 := by
    rw [luby]
    simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
  have luby1 : luby 1 = 1 := by
    rw [luby]
    simp [is_envelope, S₂, Nat.size, Nat.binaryRec]
    exact luby0
  have nsize1 : 1 ≤ (n + 1).size := by
    have t1 : (0 + 1).size ≤ (n + 1).size := by 
      refine Nat.size_le_size ?_
      exact Nat.le_add_left (0 + 1) n
    have t2 : (0 + 1).size = 1 := by simp [Nat.size, Nat.binaryRec]
    simp [t2] at t1
    exact t1
  induction' n using Nat.strong_induction_on with n nh
  {
    nth_rw 1 [luby]
    split
    { expose_names;
      have tf : is_envelope n ∨ ¬is_envelope n := by exact eq_or_ne (is_envelope n) true
      rcases tf with t|f
      {
        rw [luby]
        split
        {
          expose_names
          simp [S₂]
          have t1 : 2 * 2 ^ ((n + 1).size - 1) = 2 ^ (n + 1).size := by
            refine mul_pow_sub_one ?_ 2
            exact Nat.ne_zero_of_lt nsize1
          simp [t1]
          simp [is_envelope, S₂] at *
          have : n + 1 + 2 = n + 2 + 1 := by exact rfl
          simp only [this] at h_1
          rw [←h_1] at t
          have goal : (2 ^ ((2 ^ ((n + 2 + 1 + 1).size - 1)).size - 1)).size = (n + 2).size := by
            exact congrArg Nat.size t
          have g1 : (2 ^ ((2 ^ ((n + 2 + 1 + 1).size - 1)).size - 1)).size = 
              (2 ^ ((n + 2 + 1 + 1).size - 1)).size - 1 + 1 := by
            exact Nat.size_pow
          simp [g1] at goal
          have g2 : (2 ^ ((n + 2 + 1 + 1).size - 1)).size = (n + 2 + 1 + 1).size - 1 + 1 := by
            exact Nat.size_pow
          simp [g2] at goal



          sorry -- have : ().size = ().size := by 
        }
        sorry


      }
      simp [is_envelope] at h_1
      rw [luby]
      
      exact absurd h_1 h
    }
    { expose_names
      nth_rw 1 [luby]
      nth_rw 2 [luby]

    }


end Luby

-- 🧪 Test output
#eval List.range 24 |>.map Luby.luby
-- Output: [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1]
