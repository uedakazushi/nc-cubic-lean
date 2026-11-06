/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local CM/Koszul bridge. The local polynomial CM construction follows
StacksFrontier/RingTheory/CompleteIntersection/RingMap/Criteria.lean at
5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache-2.0).
-/
module
public import StacksFrontier.RingTheory.Koszul.Localization
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.Koszul.Relations
public import StacksFrontier.RingTheory.CohenMacaulay.MvPolynomial
public import StacksFrontier.RingTheory.CohenMacaulay.Equidimensional
import Mathlib.Tactic.Ring
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import NcCubic.GradientDimension
public import NcCubic.GradientSyzygy
public import Mathlib.Analysis.Complex.Polynomial.Basic
import Lean.Elab.Tactic.Omega
@[expose] public section
noncomputable section
namespace NcCubic.GradientRegularity
open scoped BigOperators
variable {R : Type*} [CommRing R]
private theorem ideal_ofFn {r : ℕ} (f : Fin r → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) :=
  congrArg Ideal.span (Set.ext fun _ => List.mem_ofFn)

/-- A unit generator makes every first relation a Koszul relation. This is the
local argument used away from the common zero locus. -/
theorem relation_span_of_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (j : ι) (hunit : IsUnit (g j))
    (a : ι → R) (ha : ∑ i, a i * g i = 0) :
    a ∈ Submodule.span (R)
      (Set.range fun ij : ι × ι => Pi.single ij.2 (g ij.1) - Pi.single ij.1 (g ij.2)) := by
  classical
  obtain ⟨u, hu⟩ := hunit.exists_left_inv
  let rel : ι → (ι → R) :=
    fun i => Pi.single i (g j) - Pi.single j (g i)
  have heq : a = ∑ i, (u * a i) • rel i := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, rel, Pi.sub_apply, smul_eq_mul]
    simp only [mul_sub, Finset.sum_sub_distrib]
    simp only [Pi.single_apply, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hz : (∑ x, if k = j then u * a x * g x else 0) = 0 := by
      by_cases h : k = j
      · simp only [h, ite_true, mul_assoc, ← Finset.mul_sum, ha, mul_zero]
      · simp [h]
    rw [hz, sub_zero]
    calc
      a k = (u * g j) * a k := by rw [hu, one_mul]
      _ = u * a k * g j := by ring
  rw [heq]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(j,i), rfl⟩

/-- A unit generator supplies the local H₁ vanishing away from the zero locus. -/
theorem h1Regular_of_isUnit {r : ℕ} (f : Fin r → R) (j : Fin r)
    (hj : IsUnit (f j)) : Koszul.IsH1Regular f := by
  rw [Koszul.isH1Regular_iff_forall]
  intro a ha
  exact relation_span_of_isUnit f j hj a ha

/-- Only localizations at primes containing the ideal need regular-sequence input. -/
theorem h1Regular_of_regular_at_containing_primes {r : ℕ} (f : Fin r → R)
    (hreg : ∀ (P : Ideal R) [P.IsPrime], Ideal.span (Set.range f) ≤ P →
      RingTheory.Sequence.IsRegular (Localization.AtPrime P)
        ((List.ofFn f).map (algebraMap R (Localization.AtPrime P)))) :
    Koszul.IsH1Regular f := by
  classical
  apply Koszul.isH1Regular_of_forall_localization_prime
  intro P hP
  by_cases hcontains : Ideal.span (Set.range f) ≤ P
  · have hr := hreg P hcontains
    have heq : (List.ofFn f).map (algebraMap R (Localization.AtPrime P)) =
        List.ofFn (fun j => algebraMap R (Localization.AtPrime P) (f j)) := by
      simp [Function.comp_def]
    rw [heq] at hr
    exact ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
      (R := Localization.AtPrime P) (M := Localization.AtPrime P)).2.2 hr).isH1Regular
  · have hex : ∃ j, f j ∉ P := by
      by_contra! h
      apply hcontains
      apply Ideal.span_le.mpr
      rintro x ⟨i,rfl⟩
      exact h i
    obtain ⟨j,hj⟩ := hex
    apply h1Regular_of_isUnit _ j
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (f j)).2 hj
/-- The CM dimension criterion at all primes for an isolated complete intersection.
The polynomial ring has N variables and there are exactly N equations. -/
theorem polynomial_regular_at_containing_primes_of_dimension_zero
    {K : Type*} [Field K] {N : ℕ} (f : Fin N → MvPolynomial (Fin N) K)
    (hproper : Ideal.span (Set.range f) ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ Ideal.span (Set.range f)) = 0)
    (q : Ideal (MvPolynomial (Fin N) K)) [q.IsPrime]
    (hq : Ideal.span (Set.range f) ≤ q) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      ((List.ofFn f).map (algebraMap (MvPolynomial (Fin N) K) (Localization.AtPrime q))) := by
  have hk : ∀ (p : Ideal K) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
    fun _ _ => isMaximalCohenMacaulay_self_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hS : ∀ (p : Ideal (MvPolynomial (Fin N) K)) [p.IsPrime],
      Module.IsMaximalCohenMacaulay (Localization.AtPrime p) (Localization.AtPrime p) :=
    fun p _ => Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial hk p
      (Localization.AtPrime p)
  have hd : ringKrullDim (MvPolynomial (Fin N) K) = (N : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_isField (Semifield.toIsField K), zero_add]
    simp
  have hproper' : Ideal.ofList (List.ofFn f) ≠ ⊤ := by
    simpa only [ideal_ofFn] using hproper
  have hdim' : ringKrullDim (MvPolynomial (Fin N) K ⧸ Ideal.ofList (List.ofFn f)) +
      (List.ofFn f).length ≤ (N : WithBot ℕ∞) := by
    rw [ideal_ofFn, hdim, List.length_ofFn, zero_add]
  exact (Module.IsMaximalCohenMacaulay.ringKrullDim_quotient_add_length_eq_and_isRegular
    (k := K) hS (TopologicalSpace.Equidimensional.of_preirreducibleSpace _) N hd
    (List.ofFn f) hproper' hdim').2 q (by simpa only [ideal_ofFn] using hq)
      (Localization.AtPrime q)

/-- A zero-dimensional proper intersection of N equations in affine N-space
has globally vanishing first Koszul homology. -/
theorem polynomial_h1Regular_of_dimension_zero
    {K : Type*} [Field K] {N : ℕ} (f : Fin N → MvPolynomial (Fin N) K)
    (hproper : Ideal.span (Set.range f) ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ Ideal.span (Set.range f)) = 0) :
    Koszul.IsH1Regular f :=
  h1Regular_of_regular_at_containing_primes f fun q _ hq =>
    polynomial_regular_at_containing_primes_of_dimension_zero f hproper hdim q hq
/-- The gradient of a cubic with isolated gradient zero has no syzygy
whose coefficients have total degree at most one. No regularity is assumed. -/
theorem cubic_linear_syzygy_zero {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (F : MvPolynomial (Fin N) K) (hF : F.IsHomogeneous 3)
    (hiso : ∀ x : Fin N → K, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) → x = 0)
    (a : Fin N → MvPolynomial (Fin N) K)
    (hdeg : ∀ i, (a i).totalDegree ≤ 1)
    (ha : ∑ i, a i * MvPolynomial.pderiv i F = 0) : a = 0 := by
  let g : Fin N → MvPolynomial (Fin N) K := fun i => MvPolynomial.pderiv i F
  have hg : ∀ i, (g i).IsHomogeneous 2 := fun i => by
    simpa only [g] using (hF.pderiv (i := i))
  have hm := NcCubic.GradientSyzygy.radical_span_isMaximal g (by decide : 2 ≠ 0) hg hiso
  have hproper : Ideal.span (Set.range g) ≠ ⊤ := by
    intro h
    exact hm.ne_top (Ideal.radical_eq_top.mpr h)
  have hdim := NcCubic.GradientSyzygy.quotient_dimension_zero g (by decide : 2 ≠ 0) hg hiso
  have hk := polynomial_h1Regular_of_dimension_zero g hproper hdim
  have hspan := (Koszul.isH1Regular_iff_forall g).mp hk a ha
  apply NcCubic.GradientSyzygy.eq_zero_of_mem_relation_span_of_totalDegree_lt g hg hspan
  intro i
  have hi := hdeg i
  omega
end NcCubic.GradientRegularity
