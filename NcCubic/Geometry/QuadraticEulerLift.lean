/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.CubicAmbientLift
public import NcCubic.Geometry.EulerTangentAction
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
namespace NcCubic.Geometry.QuadraticEulerLift
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ReflexiveModules
open ProjectiveCohomology

abbrev positiveEulerBundle (n : ℕ) : (ProjectiveAmbient n).Modules := twistSum ℂ n 1 (n+1)
abbrev negativeEulerDual (n : ℕ) : (ProjectiveAmbient n).Modules :=
  dualSheaf (X := ProjectiveAmbient n) (twistMinusOneSum ℂ n)
abbrev positiveBivectorBundle (n : ℕ) : (ProjectiveAmbient n).Modules :=
  Scheme.Modules.exteriorPower (positiveEulerBundle n) (2:ℤ)

/-- The fixed genuine tangent Euler quotient on exterior squares. -/
def originalEulerQuotient (n : ℕ) :
    Scheme.Modules.exteriorPower (negativeEulerDual n) (2:ℤ) ⟶
      bivectorSheaf (CotangentCoordinates.ambientProjection n) :=
  Scheme.Modules.exteriorPowerMap (eulerTangentMap ℂ n) (2:ℤ)

@[simp] theorem originalEulerQuotient_eq_sequence_g (n : ℕ) :
    originalEulerQuotient n = (tangentExteriorEulerSequence n 0).g := by
  rw [tangentExteriorEulerSequence_g]
  rfl

/-- Transport the actual positive Euler bundle into the original Euler quotient.
The isomorphism is explicit data, rather than a representability assumption. -/
def quadraticEulerMap (n : ℕ) (e : positiveEulerBundle n ≅ negativeEulerDual n) :
    positiveBivectorBundle n ⟶ bivectorSheaf (CotangentCoordinates.ambientProjection n) :=
  Scheme.Modules.exteriorPowerMap (e.hom ≫ eulerTangentMap ℂ n) (2:ℤ)

/-- Exact factorization through the original, fixed Euler quotient. -/
theorem quadraticEulerMap_eq_comp (n : ℕ) (e : positiveEulerBundle n ≅ negativeEulerDual n) :
    quadraticEulerMap n e =
      Scheme.Modules.exteriorPowerMap e.hom (2:ℤ) ≫ originalEulerQuotient n :=
  Scheme.Modules.exteriorPowerMap_comp e.hom (eulerTangentMap ℂ n) (2:ℤ)

/-- The actual map on native global sections. -/
def sectionsLinearMap (n : ℕ) (e : positiveEulerBundle n ≅ negativeEulerDual n) :
    Γ(positiveBivectorBundle n, ⊤) →ₗ[Γ(ProjectiveAmbient n, ⊤)]
      AlgebraicBivector (CotangentCoordinates.ambientProjection n) :=
  ((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).map (quadraticEulerMap n e)).hom

@[simp] theorem sectionsLinearMap_apply (n : ℕ) (e : positiveEulerBundle n ≅ negativeEulerDual n)
    (σ : Γ(positiveBivectorBundle n, ⊤)) :
    sectionsLinearMap n e σ = (quadraticEulerMap n e).app ⊤ σ := rfl

/-- Every ambient bivector has a positive Euler quadratic representative.
There is no uniqueness assertion: the tangent Euler kernel is retained. -/
theorem sectionsLinearMap_surjective (n : ℕ) (hn : 3 ≤ n)
    (e : positiveEulerBundle n ≅ negativeEulerDual n) :
    Function.Surjective (sectionsLinearMap n e) := by
  let Q := Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤
  let : Epi (Q.map (originalEulerQuotient n)) := by
    rw [originalEulerQuotient_eq_sequence_g]
    exact epi_bivectorEuler_sections n hn
  let : IsIso (Scheme.Modules.exteriorPowerMap e.hom (2:ℤ)) := inferInstance
  let : IsIso (Q.map (Scheme.Modules.exteriorPowerMap e.hom (2:ℤ))) := inferInstance
  have h : Epi (Q.map (quadraticEulerMap n e)) := by
    rw [quadraticEulerMap_eq_comp, Functor.map_comp]
    infer_instance
  exact (ModuleCat.epi_iff_surjective (Q.map (quadraticEulerMap n e))).1 h

theorem exists_quadraticEuler_lift (n : ℕ) (hn : 3 ≤ n)
    (e : positiveEulerBundle n ≅ negativeEulerDual n)
    (π : AlgebraicBivector (CotangentCoordinates.ambientProjection n)) :
    ∃ σ : Γ(positiveBivectorBundle n, ⊤), (quadraticEulerMap n e).app ⊤ σ = π :=
  sectionsLinearMap_surjective n hn e π
end NcCubic.Geometry.QuadraticEulerLift
