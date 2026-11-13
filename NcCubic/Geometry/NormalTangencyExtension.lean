module
public import NcCubic.Geometry.GenericImmersionZero
public import NcCubic.Geometry.NormalTangencyExtraction
public import NcCubic.Geometry.ProjectiveCotangentRank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry.CotangentCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry.NormalTangencyExtraction
open ProjectiveCoordinateDerivatives
variable {n : ℕ} {Y : Scheme.{0}}
/-- The normal brackets vanish on the actual hypersurface whenever the ambient
bivector restricts to its genuine intrinsic bivector. -/
theorem normal_bracket_pullback_zero_of_extension
    (ι : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (hs : ∀ i j, q j i = -q i j)
    (πP : AlgebraicBivector (ambientProjection n))
    (πY : AlgebraicBivector (ι ≫ ambientProjection n))
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (Scheme.Hom.relativeDifferentials (ambientProjection n)))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
      (bivectorSheaf (ambientProjection n))).val.app (Opposite.op ⊤) πP) =
      (ImmersionBivector.bivectorMap ι (ambientProjection n) hΩ).val.app
        (Opposite.op ⊤) πY)
    (heq : ∀ U a b, (ambientProjectiveBiderivation q hq hs).bracket U a b =
      (algebraicBivectorBracket (ambientProjection n) πP).bracket U a b) :
    ∀ i j, (ι.app (coordinateOpen i)).hom
      ((ambientProjectiveBiderivation q hq hs).bracket (coordinateOpen i)
        (normalSection F hF i) (coordinateRatio i j)) = 0 := by
  intro i j
  exact (congrArg (ι.app (coordinateOpen i)).hom
    (heq (coordinateOpen i) (normalSection F hF i) (coordinateRatio i j))).trans
    (algebraicBivectorBracket_pullback_zero_left ι (ambientProjection n) hΩ πP πY hext
      (coordinateOpen i) (normalSection F hF i) (coordinateRatio i j)
      (normalSection_pullback_zero ι F hF hideal i))
end NcCubic.Geometry.NormalTangencyExtraction
