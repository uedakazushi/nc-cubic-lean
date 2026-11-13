module
public import NcCubic.Geometry.ProjectiveCotangentRank
public import NcCubic.Geometry.BivectorMorphismCongr
public import NcCubic.Geometry.GeometricStatement
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
theorem projectionComposition_eq {n : ℕ} {Y : Scheme}
    (i : Y ⟶ ProjectiveAmbient n) :
    i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n =
      i ≫ CotangentCoordinates.ambientProjection n := rfl

def toNativeBivector {n : ℕ} {Y : Scheme} (i : Y ⟶ ProjectiveAmbient n)
    (pi : AlgebraicBivector (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)) :
    AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n) :=
  bivectorCongr (projectionComposition_eq i) pi

theorem toNativeBivector_bracket {n : ℕ} {Y : Scheme} (i : Y ⟶ ProjectiveAmbient n)
    (pi : AlgebraicBivector (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (U : Y.Opens) (a b : Γ(Y,U)) :
    (algebraicBivectorBracket (i ≫ CotangentCoordinates.ambientProjection n)
      (toNativeBivector i pi)).bracket U a b =
      (algebraicBivectorBracket (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) pi).bracket U a b :=
  algebraicBivectorBracket_bivectorCongr (projectionComposition_eq i) pi U a b
theorem exists_standardRepresentative_of_native_brackets {n : ℕ} {Y : Scheme}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F})
    (pi : AlgebraicBivector (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (h : ∃ P : Trivector (n+1), ∀ (U : Y.Opens) (a b : Γ(Y,U)),
      (algebraicBivectorBracket (i ≫ CotangentCoordinates.ambientProjection n)
        (toNativeBivector i pi)).bracket U a b =
        (hypersurfaceGlobalBracket i F P hF hideal).bracket U a b) :
    ∃ P : Trivector (n+1), HasStandardRepresentative i F hF hideal pi P := by
  obtain ⟨P,hP⟩ := h
  refine ⟨P, ?_⟩
  intro U a b
  exact (toNativeBivector_bracket i pi U a b).symm.trans (hP U a b)

end NcCubic.Geometry
