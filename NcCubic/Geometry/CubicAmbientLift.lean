/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.TangentCohomology
public import NcCubic.Geometry.AmbientBivectorLift
set_option autoImplicit false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry.CubicAmbientLift
open HypersurfaceSection HypersurfaceRestrictionSequence HypersurfaceRestrictionSections
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart
open ProjectiveCohomology AmbientBivectorLift
/-- Every genuine bivector on an actual cubic hypersurface has a canonical
ambient lift. Both cohomology vanishings are proved, not additional inputs. -/
def liftLinearMap {n : ℕ} (hn : 3 ≤ n) {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)}) :
    letI := pushforwardTopModule i (bivectorSheaf (i ≫ CotangentCoordinates.ambientProjection n))
    AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n) →ₗ[Γ(ambient n, ⊤)]
      AlgebraicBivector (CotangentCoordinates.ambientProjection n) :=
  ambientLiftLinearMap i F hF0 hideal
    (tangentBivector_cubicTwist_raw_acyclic n hn 0)
    (tangentBivector_cubicTwist_raw_acyclic n hn 1)

/-- The lift restricts through the actual closed-immersion adjunction unit to
the canonical exterior differential image. -/
theorem liftLinearMap_restrict {n : ℕ} (hn : 3 ≤ n) {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (ambientBivector n)).app ⊤
      (liftLinearMap hn i F hF0 hideal π) = ImmersionBivector.projectiveImageSection i π :=
  ambientLiftLinearMap_restrict i F hF0 hideal
    (tangentBivector_cubicTwist_raw_acyclic n hn 0)
    (tangentBivector_cubicTwist_raw_acyclic n hn 1) π

theorem liftLinearMap_injective {n : ℕ} (hn : 3 ≤ n) {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    [Smooth (i ≫ CotangentCoordinates.ambientProjection n)]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)}) :
    Function.Injective (liftLinearMap hn i F hF0 hideal) :=
  ambientLiftLinearMap_injective i F hF0 hideal
    (tangentBivector_cubicTwist_raw_acyclic n hn 0)
    (tangentBivector_cubicTwist_raw_acyclic n hn 1)
theorem liftLinearMap_ne_zero {n : ℕ} (hn : 3 ≤ n) {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    [Smooth (i ≫ CotangentCoordinates.ambientProjection n)]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) (hπ : π ≠ 0) :
    liftLinearMap hn i F hF0 hideal π ≠ 0 :=
  ambientLiftLinearMap_ne_zero i F hF0 hideal
    (tangentBivector_cubicTwist_raw_acyclic n hn 0)
    (tangentBivector_cubicTwist_raw_acyclic n hn 1) π hπ

theorem existsUnique_lift {n : ℕ} (hn : 3 ≤ n) {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃! t : AlgebraicBivector (CotangentCoordinates.ambientProjection n),
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (ambientBivector n)).app ⊤ t =
        ImmersionBivector.projectiveImageSection i π :=
  existsUnique_ambientBivector_lift i F hF0 hideal
    (tangentBivector_cubicTwist_raw_acyclic n hn 0)
    (tangentBivector_cubicTwist_raw_acyclic n hn 1) π
end NcCubic.Geometry.CubicAmbientLift
