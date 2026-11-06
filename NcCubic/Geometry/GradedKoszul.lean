/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
The elementwise exactness argument is adapted from the pinned StacksFrontier
LinearAlgebra/ExteriorPower/KoszulExact.lean (Apache-2.0); upstream notices and
licenses remain in the dependency.
-/
module
public import NcCubic.GradientRegularity
public import StacksFrontier.RingTheory.Koszul.PowerLift.UnitEntry
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.GradedKoszul
open scoped BigOperators

/-- Away from the zero locus a unit entry contracts the entire Koszul complex,
not only its first homology. -/
theorem koszulRegular_of_isUnit {R : Type*} [CommRing R] {r : ℕ}
    (f : Fin r → R) (j : Fin r) (hj : IsUnit (f j)) : Koszul.IsKoszulRegular f := by
  intro n hn
  apply Koszul.isZero_homology_seqComplex_of_span_eq_top
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨j, rfl⟩) hj

/-- Full higher Koszul regularity glues from the regular sequence at primes
containing the zero locus, and the explicit unit contraction elsewhere. -/
theorem koszulRegular_of_regular_at_containing_primes
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R)
    (hreg : ∀ (P : Ideal R) [P.IsPrime], Ideal.span (Set.range f) ≤ P →
      RingTheory.Sequence.IsRegular (Localization.AtPrime P)
        ((List.ofFn f).map (algebraMap R (Localization.AtPrime P)))) :
    Koszul.IsKoszulRegular f := by
  classical
  apply Koszul.isKoszulRegular_of_forall_localization_prime
  intro P hP
  by_cases hc : Ideal.span (Set.range f) ≤ P
  · have hr := hreg P hc
    have heq : (List.ofFn f).map (algebraMap R (Localization.AtPrime P)) =
        List.ofFn (fun j => algebraMap R (Localization.AtPrime P) (f j)) := by
      simp [Function.comp_def]
    rw [heq] at hr
    exact (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
      (R := Localization.AtPrime P) (M := Localization.AtPrime P)).2.2 hr
  · have hex : ∃ j, f j ∉ P := by
      by_contra! h
      apply hc
      exact Ideal.span_le.mpr (by rintro x ⟨i,rfl⟩; exact h i)
    obtain ⟨j,hj⟩ := hex
    exact koszulRegular_of_isUnit _ j
      ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P (f j)).2 hj)

/-- An isolated complete intersection in affine N-space has vanishing Koszul
homology in every positive degree. -/
theorem polynomial_koszulRegular_of_dimension_zero
    {K : Type*} [Field K] {N : ℕ} (f : Fin N → MvPolynomial (Fin N) K)
    (hproper : Ideal.span (Set.range f) ≠ ⊤)
    (hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ Ideal.span (Set.range f)) = 0) :
    Koszul.IsKoszulRegular f :=
  koszulRegular_of_regular_at_containing_primes f fun q _ hq =>
    GradientRegularity.polynomial_regular_at_containing_primes_of_dimension_zero
      f hproper hdim q hq

/-- The actual gradient of an isolated cubic has globally exact higher Koszul
complex. No regularity hypothesis is left to the caller. -/
theorem gradient_koszulRegular {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (F : MvPolynomial (Fin N) K) (hF : F.IsHomogeneous 3)
    (hiso : ∀ x : Fin N → K, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) → x = 0) :
    Koszul.IsKoszulRegular (fun i => MvPolynomial.pderiv i F) := by
  let g : Fin N → MvPolynomial (Fin N) K := fun i => MvPolynomial.pderiv i F
  have hg : ∀ i, (g i).IsHomogeneous 2 := fun i => by
    simpa only [g] using (hF.pderiv (i := i))
  have hm := GradientSyzygy.radical_span_isMaximal g (by decide : 2 ≠ 0) hg hiso
  have hproper : Ideal.span (Set.range g) ≠ ⊤ := by
    intro h
    exact hm.ne_top (Ideal.radical_eq_top.mpr h)
  exact polynomial_koszulRegular_of_dimension_zero g hproper
    (GradientSyzygy.quotient_dimension_zero g (by decide : 2 ≠ 0) hg hiso)

/-- Every positive-degree cycle in the actual cubic gradient complex is a
boundary. This includes exactness at polynomial bivectors (n = 1). -/
theorem gradient_cycle_is_boundary {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (F : MvPolynomial (Fin N) K) (hF : F.IsHomogeneous 3)
    (hiso : ∀ x : Fin N → K, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) → x = 0)
    (n : ℕ) (x : ⋀[MvPolynomial (Fin N) K]^(n + 1) (Fin N → MvPolynomial (Fin N) K))
    (hx : Koszul.d (Koszul.seqDual (fun i => MvPolynomial.pderiv i F)) n x = 0) :
    ∃ y : ⋀[MvPolynomial (Fin N) K]^(n + 2) (Fin N → MvPolynomial (Fin N) K),
      Koszul.d (Koszul.seqDual (fun i => MvPolynomial.pderiv i F)) (n + 1) y = x := by
  let f := fun i => MvPolynomial.pderiv i F
  have hh := gradient_koszulRegular F hF hiso (n + 1) (by omega)
  have hex : (Koszul.seqComplex f).ExactAt (n + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hh
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)] at hex
  obtain ⟨y, hy⟩ := (CategoryTheory.ShortComplex.moduleCat_exact_iff _).1 hex x (by
    show ((Koszul.seqComplex f).d (n + 1) n).hom x = 0
    rwa [Koszul.seqComplex_d f n])
  refine ⟨y, ?_⟩
  change ((Koszul.seqComplex f).d (n + 2) (n + 1)).hom y = x at hy
  rwa [Koszul.seqComplex_d f (n + 1)] at hy

end NcCubic.Geometry.GradedKoszul
