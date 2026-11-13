module
public import NcCubic.Geometry.QuadraticComponentEvaluation
public import NcCubic.Geometry.QuadraticCoefficientRatio
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
variable {n : ℕ}
theorem quadraticComponent_coefficient_bracket {S : Scheme} (f : CanonicalTwistDuality.projective ℂ n ⟶ S) (N : ℕ) (s : Set.powersetCard (Fin N) 2)
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) N ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := S) f)
    (c : MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) (a b : Γ(ProjectiveAmbient n,U)) :
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U
      ((quadraticExteriorMap f N g).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
          (ProjectiveCoordinateDerivatives.restrictedDegreeSection 2 c U))) a b =
      QuadraticCoefficientRatio.ratioQuadratic c i U hU *
      bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U
        ((quadraticExteriorMap f N g).val.app (op U)
          ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
            (CoordinateTwistFrame.frameTwo i U hU))) a b := by
  let C := (schemeModulesOfSite (CanonicalTwistDuality.projective ℂ n)).map
      (ProjectiveExteriorFrame.quadraticComponent ℂ n N s) ≫ quadraticExteriorMap f N g
  let L := (bivectorSectionBracketLinear (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U a b).comp
    (nativeSectionLinearMap (X := CanonicalTwistDuality.projective ℂ n) C U)
  have h := congrArg L (QuadraticCoefficientRatio.ratioQuadratic_smul_frameTwo c i U hU)
  exact h.symm.trans (L.map_smul (QuadraticCoefficientRatio.ratioQuadratic c i U hU)
    (CoordinateTwistFrame.frameTwo i U hU))
end NcCubic.Geometry
