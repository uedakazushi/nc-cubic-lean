/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
-/
module

public import NcCubic.Jacobian
public import NcCubic.Statement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace NcCubic.JacobianBlocks
open MvPolynomial
open scoped BigOperators
variable {R σ : Type*} [CommRing R]

/-- Mixed Jacobi identity for two potentials independent of the other active
variables. Central variables may occur in both potentials. -/
theorem compatible (i j k l m n : σ) (F G a b c : MvPolynomial σ R)
    (hFi : pderiv l F = 0) (hFj : pderiv m F = 0) (hFk : pderiv n F = 0)
    (hGi : pderiv i G = 0) (hGj : pderiv j G = 0) (hGk : pderiv k G = 0) :
    Jacobian.bracket i j k F a (Jacobian.bracket l m n G b c) +
    Jacobian.bracket i j k F b (Jacobian.bracket l m n G c a) +
    Jacobian.bracket i j k F c (Jacobian.bracket l m n G a b) +
    Jacobian.bracket l m n G a (Jacobian.bracket i j k F b c) +
    Jacobian.bracket l m n G b (Jacobian.bracket i j k F c a) +
    Jacobian.bracket l m n G c (Jacobian.bracket i j k F a b) = 0 := by
  have dFi (r : σ) : pderiv l (pderiv r F) = 0 := by rw [pderiv_comm, hFi]; simp
  have dFj (r : σ) : pderiv m (pderiv r F) = 0 := by rw [pderiv_comm, hFj]; simp
  have dFk (r : σ) : pderiv n (pderiv r F) = 0 := by rw [pderiv_comm, hFk]; simp
  have dGi (r : σ) : pderiv i (pderiv r G) = 0 := by rw [pderiv_comm, hGi]; simp
  have dGj (r : σ) : pderiv j (pderiv r G) = 0 := by rw [pderiv_comm, hGj]; simp
  have dGk (r : σ) : pderiv k (pderiv r G) = 0 := by rw [pderiv_comm, hGk]; simp
  simp only [Jacobian.bracket, map_add, map_sub, pderiv_mul]
  simp only [dFi, dFj, dFk, dGi, dGj, dGk, zero_mul, zero_add]
  simp only [pderiv_comm]
  ring

/-- Summing in the second entry of a Jacobian bracket. -/
theorem bracket_sum_right {ι : Type*} (s : Finset ι) (i j k : σ)
    (F a : MvPolynomial σ R) (b : ι → MvPolynomial σ R) :
    Jacobian.bracket i j k F a (∑ t ∈ s, b t) =
      ∑ t ∈ s, Jacobian.bracket i j k F a (b t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Jacobian.bracket]
  | @insert t s ht ih => simp [Finset.sum_insert ht, Jacobian.add_right, ih]

/-- Cancellation of an alternating array, including its diagonal, requires
no assumption excluding characteristic two. -/
theorem sum_pairwise_zero {ι A : Type*} [Fintype ι] [AddCommGroup A]
    (f : ι → ι → A) (hdiag : ∀ s, f s s = 0)
    (hpair : ∀ s t, f s t + f t s = 0) :
    ∑ s, ∑ t, f s t = 0 := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_involution (s := Finset.univ ×ˢ Finset.univ) (fun st _ => st.swap) ?_ ?_ ?_ ?_
  · intro st hst
    exact hpair st.1 st.2
  · intro st hst hn heq
    have he : st.2 = st.1 := congrArg Prod.fst heq
    exact hn (by simpa [he] using hdiag st.1)
  · intro st hst
    simp
  · intro st hst
    exact Prod.swap_swap st

/-- The bracket of a finite family of Jacobian blocks. -/
def sumBracket {ι : Type*} [Fintype ι] (x : ι → Fin 3 → σ)
    (F : ι → MvPolynomial σ R) (a b : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ s, Jacobian.bracket (x s 0) (x s 1) (x s 2) (F s) a b

/-- Independent active blocks may share any number of central variables.
The displayed derivative independence is the only support hypothesis. -/
theorem sum_jacobi {ι : Type*} [Fintype ι] (x : ι → Fin 3 → σ)
    (F : ι → MvPolynomial σ R)
    (hind : ∀ s t, s ≠ t → ∀ r : Fin 3, pderiv (x s r) (F t) = 0)
    (a b c : MvPolynomial σ R) :
    sumBracket x F a (sumBracket x F b c) +
    sumBracket x F b (sumBracket x F c a) +
    sumBracket x F c (sumBracket x F a b) = 0 := by
  classical
  simp only [sumBracket, bracket_sum_right]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib]
  apply sum_pairwise_zero
  · intro s
    exact Jacobian.jacobi _ _ _ _ _ _ _
  · intro s t
    by_cases h : s = t
    · subst t
      simp only [Jacobian.jacobi, zero_add]
    · have hh := compatible (x s 0) (x s 1) (x s 2) (x t 0) (x t 1) (x t 2)
        (F s) (F t) a b c
        (hind t s (Ne.symm h) 0) (hind t s (Ne.symm h) 1) (hind t s (Ne.symm h) 2)
        (hind s t h 0) (hind s t h 1) (hind s t h 2)
      simpa only [add_assoc] using hh


/-- Variables outside the image of a renaming do not occur after renaming. -/
theorem pderiv_rename_of_not_range {τ : Type*} (f : σ → τ) (p : MvPolynomial σ R)
    (u : τ) (hu : ∀ v, f v ≠ u) : pderiv u (rename f p) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨v, _, hv⟩ := mem_vars_rename f p h
  exact hu v hv

/-- A block potential has zero derivative in every different active block. -/
theorem block_independent {k m : ℕ} (s t : Fin k) (h : s ≠ t)
    (r : Fin 3) (f : MvPolynomial (Fin 3 ⊕ Fin m) R) :
    pderiv (Sum.inl (s, r)) (rename (NcCubic.blockVariable t) f) = 0 := by
  apply pderiv_rename_of_not_range
  intro v
  cases v with
  | inl i =>
    intro he
    have ht : t = s := congrArg Prod.fst (Sum.inl.inj he)
    exact h ht.symm
  | inr u => simp [NcCubic.blockVariable]

/-- The canonical block construction uses precisely the variable embedding
from the project's normal-form proposition. -/
def blockBracket {k m : ℕ} (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) R)
    (a b : MvPolynomial (NcCubic.BlockIndex k m) R) :
    MvPolynomial (NcCubic.BlockIndex k m) R :=
  sumBracket (fun s r => Sum.inl (s, r)) (fun s => rename (NcCubic.blockVariable s) (f s)) a b

/-- The canonical normal-form bracket satisfies Jacobi on all polynomials,
with no smoothness or homogeneity hypothesis. -/
theorem block_jacobi {k m : ℕ} (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) R)
    (a b c : MvPolynomial (NcCubic.BlockIndex k m) R) :
    blockBracket f a (blockBracket f b c) +
    blockBracket f b (blockBracket f c a) +
    blockBracket f c (blockBracket f a b) = 0 := by
  apply sum_jacobi
  exact fun s t h r => block_independent s t h r (f t)

theorem sum_skew {ι : Type*} [Fintype ι] (x : ι → Fin 3 → σ)
    (F : ι → MvPolynomial σ R) (a b : MvPolynomial σ R) :
    sumBracket x F a b = -sumBracket x F b a := by
  classical
  unfold sumBracket
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact Jacobian.skew _ _ _ _ _ _

theorem sum_add_right {ι : Type*} [Fintype ι] (x : ι → Fin 3 → σ)
    (F : ι → MvPolynomial σ R) (a b c : MvPolynomial σ R) :
    sumBracket x F a (b+c) = sumBracket x F a b + sumBracket x F a c := by
  simp only [sumBracket, Jacobian.add_right, Finset.sum_add_distrib]

theorem sum_leibniz_right {ι : Type*} [Fintype ι] (x : ι → Fin 3 → σ)
    (F : ι → MvPolynomial σ R) (a b c : MvPolynomial σ R) :
    sumBracket x F a (b*c) = sumBracket x F a b * c + b * sumBracket x F a c := by
  simp only [sumBracket, Jacobian.leibniz_right, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]

/-- A variable outside all active directions is central even if it occurs
in every potential. -/
theorem sum_other_variable_central {ι : Type*} [Fintype ι] (x : ι → Fin 3 → σ)
    (F : ι → MvPolynomial σ R) (a : MvPolynomial σ R) (u : σ)
    (hu : ∀ s r, u ≠ x s r) : sumBracket x F (X u) a = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro s _
  exact Jacobian.other_variable_central _ _ _ _ _ _ (hu s 0) (hu s 1) (hu s 2)


theorem bracket_sum_left {ι : Type*} (s : Finset ι) (i j k : σ)
    (F a : MvPolynomial σ R) (b : ι → MvPolynomial σ R) :
    Jacobian.bracket i j k F (∑ t ∈ s, b t) a =
      ∑ t ∈ s, Jacobian.bracket i j k F (b t) a := by
  rw [Jacobian.skew, bracket_sum_right, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  exact (Jacobian.skew i j k F (b t) a).symm

/-- The sum of the potentials is a Casimir for independent blocks. -/
theorem sum_potential_casimir {ι : Type*} [Fintype ι] (x : ι → Fin 3 → σ)
    (F : ι → MvPolynomial σ R)
    (hind : ∀ s t, s ≠ t → ∀ r : Fin 3, pderiv (x s r) (F t) = 0)
    (a : MvPolynomial σ R) : sumBracket x F (∑ t, F t) a = 0 := by
  classical
  unfold sumBracket
  apply Finset.sum_eq_zero
  intro s _
  rw [bracket_sum_left]
  apply Finset.sum_eq_zero
  intro t _
  by_cases h : s = t
  · subst t
    exact Jacobian.potential_casimir _ _ _ _ _
  · simp [Jacobian.bracket, hind s t h 0, hind s t h 1, hind s t h 2]

/-- Shared center variables remain central in the canonical construction. -/
theorem block_center_central {k m : ℕ} (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) R)
    (u : Fin m) (a : MvPolynomial (NcCubic.BlockIndex k m) R) :
    blockBracket f (X (Sum.inr u)) a = 0 := by
  apply sum_other_variable_central
  intro s r
  simp

/-- The original cubic, as a sum of the renamed potentials, is a Casimir. -/
theorem block_potential_casimir {k m : ℕ} (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) R)
    (a : MvPolynomial (NcCubic.BlockIndex k m) R) :
    blockBracket f (∑ s, rename (NcCubic.blockVariable s) (f s)) a = 0 := by
  apply sum_potential_casimir
  exact fun s t h r => block_independent s t h r (f t)


/-- The first coordinate bracket in every canonical block has the source
paper's sign convention. Other blocks make no contribution. -/
theorem block_coordinate01 {k m : ℕ} (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) R)
    (s : Fin k) :
    blockBracket f (X (Sum.inl (s, 0))) (X (Sum.inl (s, 1))) =
      pderiv (Sum.inl (s, 2)) (rename (NcCubic.blockVariable s) (f s)) := by
  classical
  unfold blockBracket sumBracket
  rw [Finset.sum_eq_single s]
  · apply Jacobian.coordinate_bracket <;> simp
  · intro t _ hts
    apply Jacobian.other_variable_central
    all_goals
      intro he
      have hst : s = t := congrArg Prod.fst (Sum.inl.inj he)
      exact hts hst.symm
  · simp

end NcCubic.JacobianBlocks
