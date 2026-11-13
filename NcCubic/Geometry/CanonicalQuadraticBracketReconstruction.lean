module
public import NcCubic.Geometry.CanonicalQuadraticRatioBracket
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
open CanonicalEulerCoordinateEvaluation CoordinateTwistFrame
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Sheaf CategoryTheory.sheafCompose
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
variable {n : ℕ}
theorem quadraticGlobal_ratio_bracket_of_actions
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n))
    (haction : HasCanonicalRatioAction g)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2))
    (i l m : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) :
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n) (n+1) g).val.app (op U)
        ((wedge ℂ n (twistSum ℂ n 1 (n+1)) 2).val.map (homOfLE (show U ≤ ⊤ from le_top)).op σ))
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
    ∑ s : Set.powersetCard (Fin (n+1)) 2,
      let j := Set.powersetCard.ofFinEmbEquiv.symm s 0
      let k := Set.powersetCard.ofFinEmbEquiv.symm s 1
      QuadraticCoefficientRatio.ratioQuadratic
        (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n (n+1) σ s) i U hU *
        (chartFieldValue i j l U hU * chartFieldValue i k m U hU -
          chartFieldValue i k l U hU * chartFieldValue i j m U hU) := by
  refine (quadraticGlobal_bracket_reconstruct (CotangentCoordinates.ambientProjection n) (n+1) g U σ
    (restrictedRatio i l U hU) (restrictedRatio i m U hU)).trans ?_
  apply Finset.sum_congr rfl
  intro s hs
  exact quadraticComponent_ratio_bracket_of_actions g haction s _ i l m U hU

theorem quadraticGlobal_ratio_bracket
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n))
    (hc : ∀ j : Fin (n+1), nativeFrameColumn (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) j ≫ g = canonicalEulerField ℂ n j)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2))
    (i l m : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) :
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n) (n+1) g).val.app (op U)
        ((wedge ℂ n (twistSum ℂ n 1 (n+1)) 2).val.map (homOfLE (show U ≤ ⊤ from le_top)).op σ))
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
    ∑ s : Set.powersetCard (Fin (n+1)) 2,
      let j := Set.powersetCard.ofFinEmbEquiv.symm s 0
      let k := Set.powersetCard.ofFinEmbEquiv.symm s 1
      QuadraticCoefficientRatio.ratioQuadratic
        (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n (n+1) σ s) i U hU *
        (chartFieldValue i j l U hU * chartFieldValue i k m U hU -
          chartFieldValue i k l U hU * chartFieldValue i j m U hU) := by
  exact quadraticGlobal_ratio_bracket_of_actions g (canonicalFrameColumn_action g hc) σ i l m U hU
end NcCubic.Geometry
