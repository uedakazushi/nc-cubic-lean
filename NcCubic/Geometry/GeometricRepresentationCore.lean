module
public import NcCubic.Geometry.BufferedQuadraticLift
public import NcCubic.Geometry.QuadraticProjectiveComparison
public import NcCubic.Geometry.QuadraticExtensionRepresentation
public import NcCubic.Geometry.GenericImmersionZero
public import NcCubic.Geometry.ProjectiveBivectorTransport
public import NcCubic.Geometry.ChartComparison
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace NcCubic.Geometry
open QuadraticEulerLift

/-- Equality of genuine bivectors preserves every local bracket value. -/
theorem algebraicBivectorBracket_congr_of_eq {X S : Scheme} (f : X ⟶ S)
    {pi rho : AlgebraicBivector f} (h : pi = rho) (U : X.Opens) (a b : Γ(X,U)) :
    (algebraicBivectorBracket f pi).bracket U a b =
      (algebraicBivectorBracket f rho).bracket U a b := by
  cases h
  rfl

/-- Integration lemma: genuine Euler middle data yields actual standard
representatives. The concrete canonical data will discharge its two inputs. -/
theorem exists_standardBracket_of_euler_actions_raw {n : ℕ} {Y : Scheme}
    (hn : 3 ≤ n)
    (eN : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n)
      (twistObj ℂ n 1) (n+1) ≅ negativeEulerDual n)
    (haction : HasCanonicalRatioAction (eN.hom ≫ eulerTangentMap ℂ n))
    (i : Y ⟶ CanonicalTwistDuality.projective ℂ n) [IsClosedImmersion i]
    (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F})
    (piX : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃ P : Trivector (n+1), ∀ (U : Y.Opens) (a b : Γ(Y,U)),
      (algebraicBivectorBracket (i ≫ CotangentCoordinates.ambientProjection n) piX).bracket U a b =
        (hypersurfaceGlobalBracket i F P hF hideal).bracket U a b := by
  let piP := CubicAmbientLift.liftLinearMap hn i ⟨F,hF⟩ hF0 hideal piX
  obtain ⟨σ,hσ⟩ := quadraticExteriorMap_global_surjective hn eN piP
  have hext : BivectorExtends (P := CanonicalTwistDuality.projective ℂ n) i (CotangentCoordinates.ambientProjection n)
      (CotangentCoordinates.projectiveCotangent_locallyFreeOfRank n).isFiniteLocallyFree piP piX :=
    CubicAmbientLift.liftLinearMap_restrict hn i ⟨F,hF⟩ hF0 hideal piX
  have hcomp := QuadraticProjectiveComparison.quadratic_bracket_all_opens_of_actions
    (eN.hom ≫ eulerTangentMap ℂ n) haction σ
  let q := quadraticRepresentative n σ
  let hd := quadraticRepresentative_homogeneous n σ
  let hs := quadraticRepresentative_skew n σ
  let B := ambientProjectiveBiderivation q hd hs
  have hB : ∀ U a b, B.bracket U a b =
      (algebraicBivectorBracket (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) piP).bracket U a b := by
    intro U a b
    exact (congrArg (fun D : StructureSheafBracket (ProjectiveAmbient n) => D.bracket U a b)
      (ambientProjectiveBiderivation_toBracket q hd hs)).trans
        ((hcomp U a b).symm.trans
          (algebraicBivectorBracket_congr_of_eq (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) hσ U a b))
  exact exists_standardBracket_of_quadratic_extension i F hF0 hF hgrad hideal q hd hs
    (CotangentCoordinates.projectiveCotangent_locallyFreeOfRank n).isFiniteLocallyFree
    piP piX hext hB
end NcCubic.Geometry
