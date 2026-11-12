module
public import NcCubic.Geometry.QuadraticComponentEvaluation
public import NcCubic.Geometry.QuadraticCoefficientRatio
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}
theorem quadraticComponent_coefficient_bracket (N : ℕ) (s : Set.powersetCard (Fin N) 2)
    (g : SheafExteriorFrame.sum (twistObj ℂ n 1) N ⟶ tangentSheaf (projToSpecCoeff ℂ n))
    (c : MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) (a b : Γ(ProjectiveAmbient n,U)) :
    bivectorSectionBracket (projToSpecCoeff ℂ n) U
      ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
          (ProjectiveCoordinateDerivatives.restrictedDegreeSection 2 c U))) a b =
      QuadraticCoefficientRatio.ratioQuadratic c i U hU *
      bivectorSectionBracket (projToSpecCoeff ℂ n) U
        ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
          ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
            (CoordinateTwistFrame.frameTwo i U hU))) a b := by
  rw [← QuadraticCoefficientRatio.ratioQuadratic_smul_frameTwo c i U hU]
  change bivectorSectionBracket _ _
    (((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)).hom
      (((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)).hom (_ • _))) a b = _
  rw [map_smul, map_smul, bivectorSectionBracket_smul]
end NcCubic.Geometry
