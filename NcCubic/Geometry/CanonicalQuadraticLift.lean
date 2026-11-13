module
public import NcCubic.Geometry.CanonicalEulerMiddle
public import NcCubic.Geometry.CubicQuadraticLift
@[expose] public noncomputable section
namespace NcCubic.Geometry.CanonicalQuadraticLift
open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjEulerSequence
open QuadraticEulerLift
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
/-- The standard Euler map built from literal twist multiplication duality. -/
abbrev eulerMap (n : ℕ) : positiveEulerBundle n ⟶ tangentSheaf (projToSpecCoeff ℂ n) :=
  (CanonicalEulerMiddle.positiveEulerMiddleIso ℂ n).hom ≫ eulerTangentMap ℂ n
/-- Its genuine exterior-square quotient. -/
abbrev bivectorMap (n : ℕ) : positiveBivectorBundle n ⟶ bivectorSheaf (projToSpecCoeff ℂ n) :=
  quadraticEulerMap n (CanonicalEulerMiddle.positiveEulerMiddleIso ℂ n)
 theorem exists_lift {n : ℕ} (hn : 3 ≤ n) {Y : Scheme}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme (polyGrading ℂ n) i =
      Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃ σ : Γ(positiveBivectorBundle n, ⊤),
      (bivectorMap n).app ⊤ σ = CubicAmbientLift.liftLinearMap hn i F hF0 hideal π :=
  CubicQuadraticLift.exists_lift hn (CanonicalEulerMiddle.positiveEulerMiddleIso ℂ n)
    i F hF0 hideal π
 theorem exists_lift_restrict {n : ℕ} (hn : 3 ≤ n) {Y : Scheme}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme (polyGrading ℂ n) i =
      Ideal.span {(F : MvPolynomial _ ℂ)})
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃ σ : Γ(positiveBivectorBundle n, ⊤),
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (AmbientBivectorLift.ambientBivector n)).app ⊤ ((bivectorMap n).app ⊤ σ) =
      ImmersionBivector.projectiveImageSection i π :=
  CubicQuadraticLift.exists_lift_restrict hn (CanonicalEulerMiddle.positiveEulerMiddleIso ℂ n)
    i F hF0 hideal π
end NcCubic.Geometry.CanonicalQuadraticLift
