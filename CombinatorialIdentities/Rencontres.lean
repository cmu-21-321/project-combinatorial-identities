import Mathlib


/-
Rencontres Numbers and Fixed Points of Permutations R(n, k)
The goal now is to move to a more general combinatorial identity not
already available in Mathlib

Mathlib has permutaions, fixed points, derangements, but the LLM stated
this identity is not given in the Mathlib library

R(n, k) = (n choose k) * D(n - k), where D(m) is # of derangements of m elements


-/
section Rencontres

-- Addressing TA feedback: use Mathlib's Function.fixedPoints
-- so that we can now count its elements. slight issues with
-- only using mathlib definition given the minor difference between the
-- input/output types
def fixedPoints (n : ℕ) (p : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (Function.fixedPoints (p : Fin n → Fin n)).toFinset

-- Defining R(n, k)
-- counts permutations of Fin n with exactly k fixed points
-- used set-builder for readability
def rencontres (n k : ℕ) : ℕ :=
  ({p ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) |
    (fixedPoints n p).card = k}).card

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
  simpa only [fixedPoints, Set.mem_toFinset, Function.mem_fixedPoints_iff] using hi

theorem rencontres_all_fixed (n : ℕ) : rencontres n n = 1 := by
  unfold rencontres
  have hset : {p ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))) |
    (fixedPoints n p).card = n} = {Equiv.refl (Fin n)} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact fixedPoints_all n p h
    · intro h
      subst p
      have hall :
          fixedPoints n (Equiv.refl (Fin n)) = Finset.univ := by
        ext i
        simp only [fixedPoints, Set.mem_toFinset,
          Function.mem_fixedPoints_iff, Equiv.refl_apply,
          Finset.mem_univ]
      rw [hall]
      exact Finset.card_fin n
  rw [hset]
  simp


def permsWithFixedSet (n : ℕ) (S : Finset (Fin n)) :
  Finset (Equiv.Perm (Fin n)) :=
  {p ∈ Finset.univ | fixedPoints n p = S}

theorem derangement_on_fixed_set_count (n : ℕ) (S : Finset (Fin n)) :
  (permsWithFixedSet n S).card = numDerangements (n - S.card) := by
  classical
  have hcomp : Fintype.card {x : Fin n // x ∈ Sᶜ} = n - S.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have hcondition (p : Equiv.Perm (Fin n)) :
    (∀ x, ¬ (x ∈ Sᶜ) ↔ x ∈ Function.fixedPoints p) ↔ fixedPoints n p = S := by
    simp only [Finset.mem_compl, not_not, fixedPoints,
      Finset.ext_iff, Set.mem_toFinset]
    constructor
    · intro h x
      exact (h x).symm
    · intro h x
      exact (h x).symm
  -- found some mathlib work through AI for hcount
  have hcount : Fintype.card (derangements {x : Fin n // x ∈ Sᶜ}) =
    Fintype.card {p : Equiv.Perm (Fin n) // fixedPoints n p = S} := by
    apply Fintype.card_congr
    exact (derangements.subtypeEquiv (fun x : Fin n ↦ x ∈ Sᶜ)).trans
      (Equiv.subtypeEquivRight hcondition)
  have hderangements : Fintype.card (derangements {x : Fin n // x ∈ Sᶜ}) =
    numDerangements (n - S.card) := by
    rw [card_derangements_eq_numDerangements, hcomp]
  have hperms :
      Fintype.card {p : Equiv.Perm (Fin n) // fixedPoints n p = S} =
        (permsWithFixedSet n S).card := by
    apply Fintype.card_of_subtype
    intro p
    simp [permsWithFixedSet]
  exact hperms.symm.trans (hcount.symm.trans hderangements)


theorem partition_rencontres (n k : ℕ) :
  rencontres n k = ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
  (permsWithFixedSet n S).card := by
  classical
  -- fixed point set belongs to powersetCard k when it has size k
  have hmemk (p : Equiv.Perm (Fin n)) : fixedPoints n p ∈
    Finset.powersetCard k (Finset.univ : Finset (Fin n)) ↔
    (fixedPoints n p).card = k := by
    simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
  -- count permutations of partition
  -- mathlib definition of saying counting each group and ing is the
  -- same as just counting everything
  have hpermcount :=
    Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Equiv.Perm (Fin n)))
      (Finset.powersetCard k (Finset.univ : Finset (Fin n)))
      (fun p ↦ fixedPoints n p)
  simpa only [rencontres, permsWithFixedSet, hmemk] using hpermcount.symm



-- Main theorem: the number of permutations with exactly k fixed
-- points equals the number of ways to choose those fixed points
-- times the number of derangements of the remaining elements.
-- This counting identity was not found in Mathlib from AI's inspection
theorem rencontres_formula (n k : ℕ) :
    rencontres n k = Nat.choose n k * numDerangements (n - k) := by
  rw [partition_rencontres]
  have hterm (S : Finset (Fin n))
      (hS : S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n))) :
      (permsWithFixedSet n S).card = numDerangements (n - k) := by
    have hsize : S.card = k :=
      (Finset.mem_powersetCard.mp hS).2
    rw [derangement_on_fixed_set_count, hsize]
  have hsum : (∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
    (permsWithFixedSet n S).card) =
    (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card *
    numDerangements (n - k) := by
    exact Finset.sum_const_nat hterm
  rw [hsum]
  simp

-- Quick application of theorem we just showed. Fixing exactly n - 1 points
-- would be impossible since this requires derangement of one element, which
-- is impossible.
theorem rencontres_one_unfixed (n : ℕ) (hn : 1 ≤ n) :
    rencontres n (n - 1) = 0 := by
  rw [rencontres_formula n (n - 1)]
  have hsubtract : n - (n - 1) = 1 := by omega
  rw [hsubtract]
  rw [numDerangements_one, mul_zero]

-- The zero property of rencontres with 0 fixed points. Simple rw will do.
theorem rencontres_zero_fixed (n : ℕ) :
    rencontres n 0 = numDerangements n := by
  simp [rencontres_formula]

theorem rencontres_eq_zero_of_lt (n k : ℕ) (h : n < k) :
    rencontres n k = 0 := by
  rw [rencontres_formula]
  rw [Nat.choose_eq_zero_of_lt h, zero_mul]


end Rencontres
