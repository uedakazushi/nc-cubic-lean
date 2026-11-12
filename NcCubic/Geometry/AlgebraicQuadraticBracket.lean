module
public import NcCubic.Geometry.CanonicalQuadraticBracketReconstruction
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
open CanonicalEulerCoordinateEvaluation CoordinateTwistFrame
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Sheaf CategoryTheory.sheafCompose
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}
theorem algebraicQuadratic_ratio_bracket
    (g : SheafExteriorFrame.sum (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (projToSpecCoeff ℂ n))
    (hc : ∀ j : Fin (n+1), nativeFrameColumn (X := ProjectiveAmbient n) (twistObj ℂ n 1) (n+1) j ≫ g = canonicalEulerField ℂ n j)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2))
    (i l m : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) :
    (algebraicBivectorBracket (projToSpecCoeff ℂ n)
      ((Scheme.Modules.exteriorPowerMap g 2).val.app (op ⊤) σ)).bracket U
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
    ∑ s : Set.powersetCard (Fin (n+1)) 2,
      let j := Set.powersetCard.ofFinEmbEquiv.symm s 0
      let k := Set.powersetCard.ofFinEmbEquiv.symm s 1
      QuadraticCoefficientRatio.ratioQuadratic
        (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n (n+1) σ s) i U hU *
        (chartFieldValue i j l U hU * chartFieldValue i k m U hU -
          chartFieldValue i k l U hU * chartFieldValue i j m U hU) := by
  rw [algebraicBivectorBracket_eq_sectionBracket]
  let h := (homOfLE (show U ≤ ⊤ from le_top)).op
  have hn := congrArg (fun k => k.hom σ) ((Scheme.Modules.exteriorPowerMap g 2).val.naturality h)
  change (Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
    ((wedge ℂ n (twistSum ℂ n 1 (n+1)) 2).val.map h σ) =
    (bivectorSheaf (projToSpecCoeff ℂ n)).val.map h
      ((Scheme.Modules.exteriorPowerMap g 2).val.app (op ⊤) σ) at hn
  rw [← hn]
  exact quadraticGlobal_ratio_bracket g hc σ i l m U hU
end NcCubic.Geometry
