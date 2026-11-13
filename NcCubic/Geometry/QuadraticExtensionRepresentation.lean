module
public import NcCubic.Geometry.BracketRepresentation
public import NcCubic.Geometry.GenericImmersionZero
public import NcCubic.Geometry.GeometricStatement
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
open CotangentCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Y : Scheme}
theorem exists_standardBracket_of_quadratic_extension
    (i : Y ⟶ CanonicalTwistDuality.projective ℂ n) [IsClosedImmersion i]
    (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F})
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hd : ∀ a b, (q a b).IsHomogeneous 2) (hs : ∀ a b, q b a = -q a b)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (Scheme.Hom.relativeDifferentials (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (ambientProjection n)))
    (piP : AlgebraicBivector (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (ambientProjection n))
    (piY : AlgebraicBivector (i ≫ ambientProjection n))
    (hext : BivectorExtends (P := CanonicalTwistDuality.projective ℂ n) i (ambientProjection n) hΩ piP piY)
    (heq : ∀ U a b, (ambientProjectiveBiderivation q hd hs).bracket U a b =
      (algebraicBivectorBracket (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (ambientProjection n) piP).bracket U a b) :
    ∃ P : Trivector (n+1), ∀ (U : Y.Opens) (a b : Γ(Y,U)),
      (algebraicBivectorBracket (i ≫ ambientProjection n) piY).bracket U a b =
        (hypersurfaceGlobalBracket i F P hF hideal).bracket U a b := by
  let BY := algebraicBivectorBiderivation (i ≫ ambientProjection n) piY
  have hnat := bracket_pullback_of_extends_and_eq
    (X := Y) (P := CanonicalTwistDuality.projective ℂ n) i (ambientProjection n) hΩ piP piY hext
    (ambientProjectiveBiderivation q hd hs).toStructureSheafBracket heq
  obtain ⟨P,hP⟩ := exists_standardBracket_of_quadratic_pullback
    i F hF0 hF hgrad hideal q hd hs BY hnat
  exact ⟨P,hP⟩
end NcCubic.Geometry
