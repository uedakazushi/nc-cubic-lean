module
public import NcCubic.Geometry.ProjectiveCotangentRank
public import NcCubic.Geometry.CanonicalTwistDuality
public import NcCubic.Geometry.BivectorMorphismCongr
public import NcCubic.Geometry.ProjectiveBivectorTransport
@[expose] public noncomputable section
namespace NcCubic.Geometry.ProjectiveAmbientReindex
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def rawImmersion {n : ℕ} {Y : Scheme} (i : Y ⟶ ProjectiveAmbient n) :
    Y ⟶ CanonicalTwistDuality.projective ℂ n := i

instance rawImmersion_isClosedImmersion {n : ℕ} {Y : Scheme}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i] :
    IsClosedImmersion (rawImmersion i) := by
  dsimp [rawImmersion]
  infer_instance

theorem composition_eq {n : ℕ} {Y : Scheme} (i : Y ⟶ ProjectiveAmbient n) :
    i ≫ CotangentCoordinates.ambientProjection n =
      rawImmersion i ≫ CotangentCoordinates.ambientProjection n := rfl

def toRawBivector {n : ℕ} {Y : Scheme} (i : Y ⟶ ProjectiveAmbient n)
    (pi : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    AlgebraicBivector (rawImmersion i ≫ CotangentCoordinates.ambientProjection n) :=
  bivectorCongr (composition_eq i) pi

theorem toRawBivector_bracket {n : ℕ} {Y : Scheme} (i : Y ⟶ ProjectiveAmbient n)
    (pi : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n))
    (U : Y.Opens) (a b : Γ(Y,U)) :
    (algebraicBivectorBracket (rawImmersion i ≫ CotangentCoordinates.ambientProjection n)
      (toRawBivector i pi)).bracket U a b =
      (algebraicBivectorBracket (i ≫ CotangentCoordinates.ambientProjection n) pi).bracket U a b :=
  algebraicBivectorBracket_bivectorCongr (composition_eq i) pi U a b

theorem exists_native_brackets_of_raw_brackets {n : ℕ} {Y : Scheme}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F})
    (pi : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n))
    (h : ∃ P : Trivector (n+1), ∀ (U : Y.Opens) (a b : Γ(Y,U)),
      (algebraicBivectorBracket (rawImmersion i ≫ CotangentCoordinates.ambientProjection n)
        (toRawBivector i pi)).bracket U a b =
        (hypersurfaceGlobalBracket (rawImmersion i) F P hF hideal).bracket U a b) :
    ∃ P : Trivector (n+1), ∀ (U : Y.Opens) (a b : Γ(Y,U)),
      (algebraicBivectorBracket (i ≫ CotangentCoordinates.ambientProjection n) pi).bracket U a b =
        (hypersurfaceGlobalBracket i F P hF hideal).bracket U a b := by
  obtain ⟨P,hP⟩ := h
  refine ⟨P, ?_⟩
  intro U a b
  exact (toRawBivector_bracket i pi U a b).symm.trans (hP U a b)

theorem exists_standardRepresentative_of_raw_brackets {n : ℕ} {Y : Scheme}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F})
    (pi : AlgebraicBivector (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (h : ∃ P : Trivector (n+1), ∀ (U : Y.Opens) (a b : Γ(Y,U)),
      (algebraicBivectorBracket (rawImmersion i ≫ CotangentCoordinates.ambientProjection n)
        (toRawBivector i (toNativeBivector i pi))).bracket U a b =
        (hypersurfaceGlobalBracket (rawImmersion i) F P hF hideal).bracket U a b) :
    ∃ P : Trivector (n+1), HasStandardRepresentative i F hF hideal pi P := by
  exact exists_standardRepresentative_of_native_brackets i F hF hideal pi
    (exists_native_brackets_of_raw_brackets i F hF hideal (toNativeBivector i pi) h)

end NcCubic.Geometry.ProjectiveAmbientReindex
