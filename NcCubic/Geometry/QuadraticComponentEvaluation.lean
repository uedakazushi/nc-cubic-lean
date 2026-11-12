module
public import NcCubic.Geometry.CoordinateTwistFrame
public import NcCubic.Geometry.CoordinateComponentBracket
public import NcCubic.Geometry.ProjectiveExteriorFrame
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ProjPolyChart
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u
 theorem sheafIso_inv_hom_apply {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) (z : Γ(M,U)) :
    e.inv.val.app (op U) (e.hom.val.app (op U) z) = z := by
  exact congrArg (fun k : M ⟶ M => k.val.app (op U) z) e.hom_inv_id
local instance (X : Scheme.{u}) : CategoryTheory.Limits.HasFiniteBiproducts X.Modules :=
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
def nativeFrameColumn {X : Scheme.{u}} (L : X.Modules) (N : ℕ) (j : Fin N) :
    L ⟶ SheafExteriorFrame.sum L N := CategoryTheory.Limits.biproduct.ι (fun _ : Fin N => L) j
variable {n : ℕ}
 theorem quadraticComponent_frameTwo (N : ℕ) (s : Set.powersetCard (Fin N) 2)
    (i : Fin (n+1)) (U : (CoordinateTwistFrame.ambient (n:=n)).Opens)
    (hU : U ≤ CoordinateTwistFrame.chart i) :
    (ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
      (CoordinateTwistFrame.frameTwo i U hU) =
    (SheafExteriorFrame.component (twistObj ℂ n 1) N
      (Set.powersetCard.ofFinEmbEquiv.symm s 0)
      (Set.powersetCard.ofFinEmbEquiv.symm s 1)).val.app (op U)
      ((PresheafOfModules.tensorSheafUnit (twistObj ℂ n 1) (twistObj ℂ n 1)).app (op U)
        (CoordinateTwistFrame.frameOne i U hU ⊗ₜ[_] CoordinateTwistFrame.frameOne i U hU)) := by
  rw [← CoordinateTwistFrame.frameTwo_eq_product]
  let z := (PresheafOfModules.tensorSheafUnit (twistObj ℂ n 1) (twistObj ℂ n 1)).app (op U)
    (CoordinateTwistFrame.frameOne i U hU ⊗ₜ[_] CoordinateTwistFrame.frameOne i U hU)
  let c := SheafExteriorFrame.component (twistObj ℂ n 1) N
    (Set.powersetCard.ofFinEmbEquiv.symm s 0) (Set.powersetCard.ofFinEmbEquiv.symm s 1)
  change c.val.app (op U) ((tensorTwistingSheafIso ℂ n 1 1).inv.val.app (op U)
    ((tensorTwistingSheafIso ℂ n 1 1).hom.val.app (op U) z)) = c.val.app (op U) z
  congr 1
  exact sheafIso_inv_hom_apply (tensorTwistingSheafIso ℂ n 1 1) U z

theorem quadraticComponent_frameTwo_bracket (N : ℕ) (s : Set.powersetCard (Fin N) 2)
    (g : SheafExteriorFrame.sum (twistObj ℂ n 1) N ⟶
      tangentSheaf (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (i : Fin (n+1)) (U : (CoordinateTwistFrame.ambient (n:=n)).Opens)
    (hU : U ≤ CoordinateTwistFrame.chart i) (a b : Γ(CoordinateTwistFrame.ambient (n:=n),U)) :
    bivectorSectionBracket (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) U
      ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
          (CoordinateTwistFrame.frameTwo i U hU))) a b =
      let j := Set.powersetCard.ofFinEmbEquiv.symm s 0
      let k := Set.powersetCard.ofFinEmbEquiv.symm s 1
      let v := CoordinateTwistFrame.frameOne i U hU
      let f := Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n
      tangentSectionDerivation f U (g.val.app (op U)
          ((nativeFrameColumn (X := CoordinateTwistFrame.ambient (n:=n)) (twistObj ℂ n 1) N j).val.app (op U) v)) a *
        tangentSectionDerivation f U (g.val.app (op U)
          ((nativeFrameColumn (X := CoordinateTwistFrame.ambient (n:=n)) (twistObj ℂ n 1) N k).val.app (op U) v)) b -
      tangentSectionDerivation f U (g.val.app (op U)
          ((nativeFrameColumn (X := CoordinateTwistFrame.ambient (n:=n)) (twistObj ℂ n 1) N k).val.app (op U) v)) a *
        tangentSectionDerivation f U (g.val.app (op U)
          ((nativeFrameColumn (X := CoordinateTwistFrame.ambient (n:=n)) (twistObj ℂ n 1) N j).val.app (op U) v)) b := by
  rw [quadraticComponent_frameTwo]
  exact bivectorSectionBracket_component _ _ N g _ _ U _ _ a b

end NcCubic.Geometry
