module
public import NcCubic.Geometry.BufferedExteriorSurjectivity
public import NcCubic.Geometry.CubicQuadraticLift
public import NcCubic.Geometry.QuadraticExteriorMap
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace NcCubic.Geometry
open QuadraticEulerLift
variable {n : ℕ}
-- Actual original quotient, with its source/target category spelling pinned before Γ.
theorem rawEulerQuotient_eq_sequence_g (n : ℕ) :
    Scheme.Modules.exteriorPowerMap (X := CanonicalTwistDuality.projective ℂ n)
      (eulerTangentMap ℂ n) (2:ℤ) = (ProjectiveCohomology.tangentExteriorEulerSequence n 0).g := by
  rw [ProjectiveCohomology.tangentExteriorEulerSequence_g]
  rfl

theorem quadraticExteriorMap_global_surjective (hn : 3 ≤ n)
    (eN : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n)
      (twistObj ℂ n 1) (n+1) ≅ negativeEulerDual n) :
    Function.Surjective ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n)
      (n+1) (eN.hom ≫ eulerTangentMap ℂ n)).val.app (op ⊤)) := by
  let h : negativeEulerDual n ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n)
      (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) := eulerTangentMap ℂ n
  letI : Epi ((Stacks.Cohomology.sectionsFunctor (CanonicalTwistDuality.projective ℂ n) ⊤).map
      (Scheme.Modules.exteriorPowerMap (X := CanonicalTwistDuality.projective ℂ n) h (2:ℤ))) := by
    change Epi ((Stacks.Cohomology.sectionsFunctor (CanonicalTwistDuality.projective ℂ n) ⊤).map
      (Scheme.Modules.exteriorPowerMap (X := CanonicalTwistDuality.projective ℂ n) (eulerTangentMap ℂ n) (2:ℤ)))
    rw [rawEulerQuotient_eq_sequence_g]
    exact ProjectiveCohomology.epi_bivectorEuler_sections n hn
  exact BufferedExteriorSurjectivity.bufferedMap_global_surjective
    (CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) 2 eN h

/-- The new buffered quadratic lift obeys the literal original immersion unit. -/
theorem exists_buffered_quadratic_lift_restrict {Y : Scheme} (hn : 3 ≤ n)
    (eN : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n)
      (twistObj ℂ n 1) (n+1) ≅ negativeEulerDual n)
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme (polyGrading ℂ n) i =
      Ideal.span {(F : MvPolynomial _ ℂ)})
    (pi : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃ σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2),
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (AmbientBivectorLift.ambientBivector n)).app ⊤
        ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n)
          (n+1) (eN.hom ≫ eulerTangentMap ℂ n)).val.app (op ⊤) σ) =
        ImmersionBivector.projectiveImageSection i pi := by
  obtain ⟨σ,hσ⟩ := quadraticExteriorMap_global_surjective hn eN
    (CubicAmbientLift.liftLinearMap hn i F hF0 hideal pi)
  refine ⟨σ, ?_⟩
  rw [hσ]
  exact CubicAmbientLift.liftLinearMap_restrict hn i F hF0 hideal pi
end NcCubic.Geometry
