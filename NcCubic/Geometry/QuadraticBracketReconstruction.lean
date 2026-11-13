module
public import NcCubic.Geometry.QuadraticLocalReconstruction
public import NcCubic.Geometry.QuadraticCoefficientBracket
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
variable {n : ℕ}
theorem quadraticLocal_bracket_reconstruct {S : Scheme} (f : CanonicalTwistDuality.projective ℂ n ⟶ S) (N : ℕ)
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) N ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := S) f)
    (U : (ProjectiveAmbient n).Opens)
    (σ : (wedge ℂ n (twistSum ℂ n 1 N) 2).val.obj (op U)) (a b : Γ(ProjectiveAmbient n,U)) :
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U
      ((quadraticExteriorMap f N g).val.app (op U) σ) a b =
    ∑ s : Set.powersetCard (Fin N) 2,
      bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U
        ((quadraticExteriorMap f N g).val.app (op U)
          ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
            ((ProjectiveExteriorFrame.quadraticProjection ℂ n N s).val.app (op U) σ))) a b := by
  let L := (bivectorSectionBracketLinear (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U a b).comp
    (nativeSectionLinearMap (X := CanonicalTwistDuality.projective ℂ n) (quadraticExteriorMap f N g) U)
  change L σ = ∑ s, L _
  exact (congrArg L (quadraticLocal_reconstruct n N U σ).symm).trans
    (map_sum L (fun s : Set.powersetCard (Fin N) 2 =>
      (ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticProjection ℂ n N s).val.app (op U) σ)) Finset.univ)

theorem quadraticGlobal_bracket_reconstruct {S : Scheme} (f : CanonicalTwistDuality.projective ℂ n ⟶ S) (N : ℕ)
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) N ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := S) f)
    (U : (ProjectiveAmbient n).Opens)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 N) 2))
    (a b : Γ(ProjectiveAmbient n,U)) :
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U
      ((quadraticExteriorMap f N g).val.app (op U)
        ((wedge ℂ n (twistSum ℂ n 1 N) 2).val.map (homOfLE (show U ≤ ⊤ from le_top)).op σ)) a b =
    ∑ s : Set.powersetCard (Fin N) 2,
      bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U
        ((quadraticExteriorMap f N g).val.app (op U)
          ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
            (ProjectiveCoordinateDerivatives.restrictedDegreeSection 2
              (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n N σ s) U))) a b := by
  refine (quadraticLocal_bracket_reconstruct f N g U _ a b).trans ?_
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun z : (twistObj ℂ n 2).val.obj (op U) =>
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := S) f U
      ((quadraticExteriorMap f N g).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U) z)) a b)
    (quadraticProjection_restrict n N U σ s)
end NcCubic.Geometry
