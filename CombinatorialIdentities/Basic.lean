import Mathlib

--import Mathlib.Tactic.MinImports
/-
This project tries to explore binomial coefficients and classic
combinatorial identities in lean

I want to start by proving some basic theorems like Pascal's, Binomial sums,
and symmetry within. Later I want to use these baseline proofs to dive
into deeper competition level proofs

def choose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

from Mathlib/Data/Nat/Choose
theorem choose_zero_right (n : ℕ) : choose n 0 = 1 := by cases n <;> rfl
-/

-- Warming up with basic proofs
#check Nat.choose
#check Nat.choose_zero_right
#eval Nat.choose 5 2


theorem choose_zero (n : ℕ) : Nat.choose n 0 = 1 := by
  cases n <;> rfl

theorem pascals_identity (n k : ℕ) :
  Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1):= by
  exact Nat.choose_succ_succ' n k

theorem choose_le_plus_one (n k : ℕ) :
  Nat.choose n k ≤ Nat.choose (n + 1) (k + 1) := by
  rw[pascals_identity]
  omega

theorem choose_symmetry (n k : ℕ) (h : k ≤ n) :
  Nat.choose n k = Nat.choose n (n - k) := by
  exact Eq.symm (Nat.choose_symm h)


-- Binomial sum identity with all coefficients in one row
-- all summing to 2^n
-- Looked up how to represent summation in Lean (+ Finset) and
-- skeleton of induction proofs
theorem binomial_sum (n : ℕ) :
  (∑ k ∈ Finset.range (n + 1), Nat.choose n k) = 2 ^ n := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hstep :
      Finset.sum (Finset.range (n + 2)) (fun k => Nat.choose (n + 1) k) =
      2 * Finset.sum (Finset.range (n + 1)) (fun k => Nat.choose n k) := by
      rw [Finset.sum_range_succ']
      -- looked up how to rewrite across a sum in Finset (simp_rw)
      simp_rw [pascals_identity]
      rw [Finset.sum_add_distrib]
      rw [choose_zero]
      rw [Nat.add_assoc]
      rw [Nat.two_mul]
      rw [Nat.add_left_cancel_iff]
      -- only rewriting the right side (looked it up)
      conv_rhs =>
        rw [Finset.sum_range_succ']
      rw [Finset.sum_range_succ]
      simp
    rw[hstep, ih]
    ring


section AMC10B_12

/-
https://artofproblemsolving.com/wiki/index.php?title=2024_AMC_10B_Problems/Problem_12
Testing out current identities to formalize 2024 AMC10B #12
A group of 100 students from different countries meet at a
mathematics competition. Each student speaks the same number of languages,
and, for every pair of students A and B, student A speaks some language
that student B does not speak, and student B speaks some language that student
A does not speak. What is the least possible total number of languages
spoken by all the students?

Represent languages for each student as Finset, first showing
that two sets of same size but different sets must each contain element the
other does not.

Althought he question gives it as an assumption, given that there's an
"answer" to the question we modify it a bit here.
-/



theorem AMC10B_12_different_sets (A B : Finset ℕ)
  (hcard : A.card = B.card) (hne : A ≠ B) : ∃ x, x ∈ A ∧ x ∉ B := by
  by_contra h
  have hsubset : A ⊆ B := by
    intro x hxa
    by_contra hnb
    apply h
    use x
  have heq : A = B := by
    -- Looked up needed theorem
    apply Finset.eq_of_subset_of_card_le hsubset
    omega
  exact hne heq

-- We are going to show both directions
theorem AMC10B_12_different_language (A B : Finset ℕ)
  (hcard : A.card = B.card) (hne : A ≠ B) : (∃ x, x ∈ A ∧ x ∉ B) ∧
  (∃ x, x ∈ B ∧ x ∉ A) := by
  constructor
  · exact AMC10B_12_different_sets A B hcard hne
  · apply AMC10B_12_different_sets B A
    · exact hcard.symm
    · intro hba
      exact hne hba.symm

variable (n k : ℕ)
variable (f : Fin 100 → Finset (Fin n))
variable (hcard : ∀ s, (f s).card = k)
variable (hinj : Function.Injective f)

include hcard hinj

-- Dove into the Finset mathlib
-- https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Data/Finset

#check Finset.card_image_of_injective
theorem AMC10B_12_counting_lowerbound : 100 ≤ Nat.choose n k := by
  have hsetsize : --using Mathlib
    ((Finset.univ : Finset (Fin n)).powersetCard k).card =
    Nat.choose n k := by
    simp
  have hmember (s : Fin 100) :
    f s ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
    simp [Finset.mem_powersetCard, hcard s]
  have himage : (Finset.univ.image f).card = 100 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hsubset : Finset.univ.image f ⊆
    (Finset.univ : Finset (Fin n)).powersetCard k := by
    intro h hI
    rcases Finset.mem_image.mp hI with ⟨a, ha, rfl⟩
    exact hmember a
  have hle := Finset.card_le_card hsubset
  rw[himage, hsetsize] at hle
  exact hle

theorem AMC10B_12_counting_upperbound : n ≤ 8 → Nat.choose n k < 100 := by
  intro hn
  by_cases hk : k ≤ n
  · interval_cases n
    all_goals interval_cases k
    all_goals norm_num [Nat.choose]
    -- Learned intervalcases and notation for the case work from below
    -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/IntervalCases.html
  · have hkn : n < k := by omega
    simp [Nat.choose_eq_zero_of_lt hkn]

-- finalizing proof
#check AMC10B_12_counting_upperbound

theorem AMC10B_12_finalizing : 9 ≤ n := by
  by_contra h
  have hn : n ≤ 8 := by
    omega
  have hlower : 100 ≤ Nat.choose n k := by
    exact AMC10B_12_counting_lowerbound n k f hcard hinj
  have hupper : Nat.choose n k < 100 := by
    exact AMC10B_12_counting_upperbound n k f hcard hinj hn
  omega



end AMC10B_12

section AMC10A_10

/-
Consider the following operation. Given a positive integer n, if n is a
multiple of 3, then you replace n by n/3. If n is not a multiple of 3,
then you replace n by n+10. Then continue this process. For example,
beginning with n=4, this procedure gives 4,14,24,8,18,6,2,12...
Suppose you start with n=100. What value results if you perform this operation
exactly 100 times?

We want to use recursion to solve
-/


-- Define operation
def operation (n : ℕ) : ℕ :=
  if n % 3 = 0 then n / 3 else n + 10

def repeatOperation (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => operation (repeatOperation n k)

#eval operation 100
#eval operation 4
#eval operation 14
#eval repeatOperation 4 3

theorem AMC10A_10_10to3 : repeatOperation 10 3 = 10 := by
  sorry

theorem AMC10A_10_repeating10s (m : ℕ) :
  repeatOperation 10 (3 * m) = 10 := by
  sorry

theorem AMC10A_10_10_steps : repeatOperation 100 8 = 10 := by
  sorry

theorem AMC10A_10_finalizing : repeatOperation 100 100 = 20 := by
  sorry




end AMC10A_10

/-
Rencontres Numbers and Fixed Points of Permutations R(n, k)
The goal now is to move to a more general combinatorial identity not
already available in Mathlib

Mathlib has permuations, fixed points, derangements, but the LLM stated
this identity is not given in the Mathlib library

R(n, k) = (n choose k) * D(n - k), where D(m) is # of derangements of m elements


-/
section Rencontres

def fixedPoints (n : ℕ) (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i = i)

-- Defining R(n, k)
-- counts permutations of Fin n with exactly k fixed points
def rencontres (n k : ℕ) : ℕ := (Finset.univ.filter (fun p : Equiv.Perm (Fin n )
   => (fixedPoints n p).card = k)).card

-- Proving R(n, n) = 1
theorem fixedPoints_all (n : ℕ) (p : Equiv.Perm (Fin n))
    (h : (fixedPoints n p).card = n) :
    p = Equiv.refl (Fin n) := by
  apply Equiv.ext
  intro i
  simp only [Equiv.refl_apply]
  have hsub : fixedPoints n p ⊆ Finset.univ := by
    intro x hx
    simp
  have hcard : (Finset.univ : Finset (Fin n)).card ≤ (fixedPoints n p).card := by
    simp [h]
  have hall : fixedPoints n p = Finset.univ := by
    exact Finset.eq_of_subset_of_card_le hsub hcard
  have hi : i ∈ fixedPoints n p := by
    rw [hall]
    simp
  simp only [fixedPoints, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact hi

def permsWithFixedSet (n : ℕ) (S : Finset (Fin n)) :
  Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p ↦ fixedPoints n p = S)

theorem derangement_on_fixed_set_count (n : ℕ) (S : Finset (Fin n)) :
  (permsWithFixedSet n S).card = numDerangements (n - S.card) := by
  sorry

theorem partition_rencontres (n k : ℕ) :
  rencontres n k = ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
  (permsWithFixedSet n S).card := by
  sorry



-- Main theorem: the number of permutations with exactly k fixed
-- points equals the number of ways to choose those fixed points
-- times the number of derangements of the remaining elements.
-- This counting identity was not found in Mathlib from AI's inspection
theorem rencontres_formula (n k : ℕ) (hk : k ≤ n) :
    rencontres n k = Nat.choose n k * numDerangements (n - k) := by
  sorry



end Rencontres







--#min-imports
