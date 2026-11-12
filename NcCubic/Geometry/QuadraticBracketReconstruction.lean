module
public import NcCubic.Geometry.QuadraticLocalReconstruction
public import NcCubic.Geometry.QuadraticCoefficientBracket
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}
theorem quadraticLocal_bracket_reconstruct (N : ℕ)
    (g : SheafExteriorFrame.sum (twistObj ℂ n 1) N ⟶ tangentSheaf (projToSpecCoeff ℂ n))
    (U : (ProjectiveAmbient n).Opens)
    (σ : (wedge ℂ n (twistSum ℂ n 1 N) 2).val.obj (op U)) (a b : Γ(ProjectiveAmbient n,U)) :
    bivectorSectionBracket (projToSpecCoeff ℂ n) U
      ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U) σ) a b =
    ∑ s : Set.powersetCard (Fin N) 2,
      bivectorSectionBracket (projToSpecCoeff ℂ n) U
        ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
          ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
            ((ProjectiveExteriorFrame.quadraticProjection ℂ n N s).val.app (op U) σ))) a b := by
  let L := (bivectorSectionBracketLinear (projToSpecCoeff ℂ n) U a b).comp
    ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)).hom
  change L σ = ∑ s, L _
  rw [← map_sum]
  exact congrArg L (quadraticLocal_reconstruct n N U σ).symm

theorem quadraticGlobal_bracket_reconstruct (N : ℕ)
    (g : SheafExteriorFrame.sum (twistObj ℂ n 1) N ⟶ tangentSheaf (projToSpecCoeff ℂ n))
    (U : (ProjectiveAmbient n).Opens)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 N) 2))
    (a b : Γ(ProjectiveAmbient n,U)) :
    bivectorSectionBracket (projToSpecCoeff ℂ n) U
      ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
        ((wedge ℂ n (twistSum ℂ n 1 N) 2).val.map (homOfLE (show U ≤ ⊤ from le_top)).op σ)) a b =
    ∑ s : Set.powersetCard (Fin N) 2,
      bivectorSectionBracket (projToSpecCoeff ℂ n) U
        ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
          ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
            (ProjectiveCoordinateDerivatives.restrictedDegreeSection 2
              (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n N σ s) U))) a b := by
  rw [quadraticLocal_bracket_reconstruct]
  apply Finset.sum_congr rfl
  intro s hs
  rw [quadraticProjection_restrict]
end NcCubic.Geometry
