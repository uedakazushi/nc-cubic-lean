/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Focused adaptation of ProjectiveSpaceHodgeCohomology, pinned AxiomMath/Stacks
5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache 2.0), retaining only Serre
cohomology, derived global sections, and finite twisting-sheaf sums.
No Hodge-Chern, de Rham, or different-divisor module is imported. -/
module
public import StacksFrontier.Algebra.Homology.RightDerivedDelta
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] Stacks.AlgebraicGeometry.ProjTwistRank.hasFiniteBiproducts_toRingCat
namespace NcCubic.Geometry.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveSpace.Cohomology
theorem isZero_restrictScalars_iff {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (Z : ModuleCat.{u} S) :
    IsZero ((ModuleCat.restrictScalars f).obj Z) ↔ IsZero Z := by
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-! ### The setting -/

variable (A : Type u) [CommRing A] (m : ℕ)

/-- `ℙⁿ_A = Proj A[T₀, …, Tₙ]` with `n = m + 1`. -/
abbrev projSpace : Scheme.{u} := AlgebraicGeometry.Proj (polyGrading A (m + 1))

/-- Global sections on `ℙⁿ_A`, the functor whose right derived functors are the cohomology. -/
abbrev globalSections : (projSpace A m).Modules ⥤ ModuleCat.{u} Γ(projSpace A m, ⊤) :=
  Stacks.Cohomology.sectionsFunctor (projSpace A m) ⊤

/-- `H^q(ℙⁿ_A, ℱ)` as a module over the global functions on `ℙⁿ_A`. -/
abbrev cohomologySheaf (F : (projSpace A m).Modules) (q : ℕ) :
    ModuleCat.{u} Γ(projSpace A m, ⊤) :=
  ((globalSections A m).rightDerived q).obj F

/-- `H^q(ℙⁿ_A, ℱ)` as an `A`-module, the coefficients acting through the structure morphism
`ℙⁿ_A ⟶ Spec A`. This is the reading of
`Stacks.ProjectiveSpace.Cohomology.twistCohomology`, extended from the twists to an arbitrary
sheaf of modules. -/
abbrev cohomology (F : (projSpace A m).Modules) (q : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars.{u} (coeffScalar A (m + 1))).obj (cohomologySheaf A m F q)


instance additive_rightDerived_globalSections (q : ℕ) :
    ((globalSections A m).rightDerived q).Additive :=
  (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (globalSections A m)).additive q

variable {A m}

/-- The polynomial chart of negative degree is a subsingleton, which is the vanishing that drives
both extreme-degree cases of Serre's computation. -/
private theorem subsingleton_twistChart_empty {d : ℤ} (hd : d < 0) :
    Subsingleton ↥(twistChart A (m + 1) d (∅ : Set (Fin (m + 1 + 1)))) := by
  rw [twistChart_eq_bot_of_neg (R := A) (m + 1) hd]
  infer_instance

/-- `H⁰(ℙⁿ_A, 𝒪(d)) = 0` for `d < 0`. -/
private theorem isZero_twistCohomology_zero {d : ℤ} (hd : d < 0) :
    IsZero (twistCohomology A (m + 1) d 0) :=
  IsZero.of_iso (ModuleCat.isZero_of_iff_subsingleton.2 (subsingleton_twistChart_empty hd))
    (serreTwistCohomology A m d).degreeZero

/-- `Hⁿ(ℙⁿ_A, 𝒪(d)) = 0` for `-n ≤ d`. -/
private theorem isZero_twistCohomology_top {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) :
    IsZero (twistCohomology A (m + 1) d (m + 1)) := by
  have hneg : -d - (((m + 1 : ℕ) : ℤ) + 1) < 0 := by push_cast; omega
  have hs := subsingleton_twistChart_empty (A := A) (m := m) hneg
  have hhom : Subsingleton (↥(twistChart A (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1))
      (∅ : Set (Fin (m + 1 + 1)))) →ₗ[A] A) :=
    ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp⟩
  exact IsZero.of_iso (ModuleCat.isZero_of_iff_subsingleton.2 hhom)
    (serreTwistCohomology A m d).degreeTop

/-- **`H^q(ℙⁿ_A, 𝒪(d)) = 0` for `q > 0` and `-n ≤ d`.** The case of Serre's computation
([Stacks, Tag 01XU]) that the proof of [Stacks, Tag 0FUK] quotes for the twisted sequences. -/
theorem isZero_twistCohomology_of_pos {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) {q : ℕ} (hq : 0 < q) :
    IsZero (twistCohomology A (m + 1) d q) := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  rcases eq_or_ne (r + 1) (m + 1) with h | h
  · rw [h]
    exact isZero_twistCohomology_top hd
  · exact (serreTwistCohomology A m d).vanishing r h

/-- **`H^q(ℙⁿ_A, 𝒪(d)) = 0` in every degree for `-n ≤ d < 0`.** This is the statement the source
uses as "`𝒪(-1)` has vanishing cohomology in all degrees", in the range of twists where it
holds. -/
theorem isZero_twistCohomology_of_neg {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) (hd' : d < 0) (q : ℕ) :
    IsZero (twistCohomology A (m + 1) d q) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact isZero_twistCohomology_zero hd'
  · exact isZero_twistCohomology_of_pos hd hq

/-- **The acyclicity of the twists of the structure sheaf on `ℙⁿ_A`**, as a statement about the
sheaf-level cohomology: in every degree for `-n ≤ d < 0`, and in every positive degree for
`-n ≤ d`. -/
theorem isZero_cohomologySheaf_twistingSheaf {d : ℤ} (hd : -((m : ℤ) + 1) ≤ d) (q : ℕ)
    (hq : d < 0 ∨ 0 < q) :
    IsZero (cohomologySheaf A m
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) d) q) := by
  refine (isZero_restrictScalars_iff (coeffScalar A (m + 1)) _).1 ?_
  rcases hq with hq | hq
  · exact isZero_twistCohomology_of_neg hd hq q
  · exact isZero_twistCohomology_of_pos hd hq

/-- The degree-zero part of `A[T₀, …, Tₙ]` is `A`: the constants. -/
def twistChartZeroEquiv : ↥(twistChart A (m + 1) 0 (∅ : Set (Fin (m + 1 + 1)))) ≃ₗ[A] A :=
  (twistChartEmptyLinearEquiv (R := A) (m + 1) (le_refl (0 : ℤ))).trans
    ((LinearEquiv.ofEq _ _ (by
        rw [show ((0 : ℤ)).toNat = 0 from rfl, MvPolynomial.homogeneousSubmodule_zero,
          Submodule.one_eq_range])).trans
      (LinearEquiv.ofInjective (Algebra.linearMap A (MvPolynomial (Fin (m + 1 + 1)) A))
        (fun _ _ hxy => MvPolynomial.C_injective _ _ hxy)).symm)

/-- **`H⁰(ℙⁿ_A, 𝒪) = A`.** The generator the source takes the boundary of is `1`. -/
def twistingSheafZeroCohomologyIso :
    cohomology A m (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) 0) 0 ≅
      ModuleCat.of A A :=
  (serreTwistCohomology A m 0).degreeZero ≪≫ (twistChartZeroEquiv (A := A) (m := m)).toModuleIso


theorem isZero_cohomologySheaf_biproduct {k : ℕ}
    (G : Fin k → (projSpace A m).Modules) (q : ℕ)
    (h : ∀ i, IsZero (cohomologySheaf A m (G i) q)) :
    IsZero (cohomologySheaf A m (⨁ G) q) := by
  refine IsZero.of_iso ?_ (((globalSections A m).rightDerived q).mapBiproduct G)
  rw [IsZero.iff_id_eq_zero]
  refine biproduct.hom_ext' _ _ fun i => ?_
  rw [Category.comp_id, Limits.comp_zero]
  exact (h i).eq_of_src _ _


variable (A m)

/-- The negative line bundles occurring in the cubic Euler complexes are acyclic
in all derived global-section degrees. Here projective space has dimension `m+1`. -/
theorem negative_twist_acyclic (hm : 3 ≤ m + 1) (r : ℕ)
    (hr : 1 ≤ r) (hr' : r ≤ 3) (q : ℕ) :
    IsZero (cohomologySheaf A m
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A (m + 1)) (-(r : ℤ))) q) := by
  exact isZero_cohomologySheaf_twistingSheaf (by omega) q (Or.inl (by omega))

/-- Every finite direct sum of the negative twists needed in the tangent
Euler resolution is acyclic as an actual projective-space sheaf. -/
theorem negative_twistSum_acyclic (hm : 3 ≤ m + 1) (r : ℕ)
    (hr : 1 ≤ r) (hr' : r ≤ 3) (s q : ℕ) :
    IsZero (cohomologySheaf A m
      (Stacks.AlgebraicGeometry.ProjTwistRank.twistSum A (m + 1) (-(r : ℤ)) s) q) := by
  exact isZero_cohomologySheaf_biproduct
    (Stacks.AlgebraicGeometry.ProjTwistRank.twistFamily A (m + 1) (-(r : ℤ)) s)
    q (fun _ => negative_twist_acyclic A m hm r hr hr' q)


end NcCubic.Geometry.ProjectiveCohomology
