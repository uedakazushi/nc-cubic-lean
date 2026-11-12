/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.QuadraticEulerLift
set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry.CubicQuadraticLift
open Stacks.AlgebraicGeometry.ProjPolyChart
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open QuadraticEulerLift AmbientBivectorLift

/-- Every genuine hypersurface bivector admits a positive Euler quadratic lift.
The chosen middle-bundle isomorphism is explicit data; no representability is assumed. -/
theorem exists_lift {n : ℕ} (hn : 3 ≤ n)
    (e : positiveEulerBundle n ≅ negativeEulerDual n) {Y : Scheme.{0}}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃ σ : Γ(positiveBivectorBundle n, ⊤),
      (quadraticEulerMap n e).app ⊤ σ = CubicAmbientLift.liftLinearMap hn i F hF0 hideal π :=
  exists_quadraticEuler_lift n hn e (CubicAmbientLift.liftLinearMap hn i F hF0 hideal π)

/-- The lifted section has the actual closed-immersion restriction equation. -/
theorem exists_lift_restrict {n : ℕ} (hn : 3 ≤ n)
    (e : positiveEulerBundle n ≅ negativeEulerDual n) {Y : Scheme.{0}}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃ σ : Γ(positiveBivectorBundle n, ⊤),
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (ambientBivector n)).app ⊤
        ((quadraticEulerMap n e).app ⊤ σ) = ImmersionBivector.projectiveImageSection i π := by
  obtain ⟨σ, hσ⟩ := exists_lift hn e i F hF0 hideal π
  refine ⟨σ, ?_⟩
  rw [hσ]
  exact CubicAmbientLift.liftLinearMap_restrict hn i F hF0 hideal π

/-- A nonzero bivector on a genuinely smooth hypersurface has a nonzero lift.
No uniqueness of the positive Euler section is asserted. -/
theorem exists_nonzero_lift {n : ℕ} (hn : 3 ≤ n)
    (e : positiveEulerBundle n ≅ negativeEulerDual n) {Y : Scheme.{0}}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    [Smooth (i ≫ CotangentCoordinates.ambientProjection n)]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) (hπ : π ≠ 0) :
    ∃ σ : Γ(positiveBivectorBundle n, ⊤), σ ≠ 0 ∧
      (quadraticEulerMap n e).app ⊤ σ = CubicAmbientLift.liftLinearMap hn i F hF0 hideal π := by
  obtain ⟨σ, hσ⟩ := exists_lift hn e i F hF0 hideal π
  refine ⟨σ, ?_, hσ⟩
  intro hσ0
  apply CubicAmbientLift.liftLinearMap_ne_zero hn i F hF0 hideal π hπ
  exact hσ.symm.trans (by rw [hσ0]; exact map_zero _)
end NcCubic.Geometry.CubicQuadraticLift
