import Mathlib

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
