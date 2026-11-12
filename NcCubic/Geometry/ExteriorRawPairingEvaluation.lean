module
public import NcCubic.Geometry.ExteriorRawPairingCore
public import NcCubic.Geometry.ExteriorDescentApply
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false

variable {C : Type u} [Category.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (P Q : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)) (U : C) (n : ℕ)
set_option backward.isDefEq.respectTransparency false

theorem extPowOverIso_wedge (Z : (Over U)ᵒᵖ)
    (v : Fin n → P.obj (op Z.unop.left)) :
    ((PresheafOfModules.extPowOverIso (O:=O) U n P).hom.app Z)
      (PresheafExterior.wedgeSection.{u,u,u,u} P n (op Z.unop.left) v) =
    PresheafExterior.wedgeSection.{u,u,u,u} (O := (Over.forget U).op ⋙ O) ((restrFun O U).obj P) n Z v := by
  rfl

theorem overExteriorFunctional_wedge
    (d : PresheafOfModules.extPow (O := (Over.forget U).op ⋙ O) n
        ((restrFun O U).obj P) ⟶ (restrFun O U).obj Q)
    (Z : (Over U)ᵒᵖ) (v : Fin n → P.obj (op Z.unop.left)) :
    (overExteriorFunctional O P Q U n d).app Z
      (PresheafExterior.wedgeSection.{u,u,u,u} P n (op Z.unop.left) v) =
    d.app Z (PresheafExterior.wedgeSection.{u,u,u,u} (O := (Over.forget U).op ⋙ O) ((restrFun O U).obj P) n Z v) := by
  change d.app Z (((PresheafOfModules.extPowOverIso (O:=O) U n P).hom.app Z)
    (PresheafExterior.wedgeSection.{u,u,u,u} P n (op Z.unop.left) v)) = _
  exact congrArg (fun z => d.app Z z) (extPowOverIso_wedge O P U n Z v)

/-- The computed raw local exterior functional has the determinant value on
actual sectionwise exterior generators, with no choice of sheaf isomorphism. -/
theorem localRawExteriorPairing_eval_wedge {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (lam mu : Γ(dualSheaf M,U)) (v : Fin 2 → Γ(M,U)) :
    (localRawExteriorPairing M lam mu).app (op (Over.mk (𝟙 U)))
      (exteriorRawWedge M U
        (fun i => (siteSectionSemilinearEquiv M U).symm (v i))) =
      evalAt M lam (v 0) * evalAt M mu (v 1) -
        evalAt M mu (v 0) * evalAt M lam (v 1) := by
  have hc := overExteriorFunctional_wedge X.sheaf.obj
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M)
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (SheafOfModules.unit X.ringCatSheaf)) U 2
      (eqToHom (congrArg (fun F => PresheafOfModules.extPow
          (O := (X.sheaf.over U).obj) 2 F) (sliceRawModule_eq M U)) ≫
        localDeterminantPresheaf M lam mu ≫ eqToHom (sliceRawUnit_eq X U))
      (op (Over.mk (𝟙 U)))
      (fun i => (siteSectionSemilinearEquiv M U).symm (v i))
  have hd := PresheafExterior.desc_wedgeSection.{u,u,u,u} (O := (X.sheaf.over U).obj)
    (SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
      (SliceModule M U)) 2
    (fun Z => dualDeterminantRawAlternating M lam mu Z)
    (fun k w => dualDeterminantRawAlternating_natural M lam mu k w)
    (op (Over.mk (𝟙 U)))
    (fun i => (sliceSectionEquiv M U (op (Over.mk (𝟙 U)))).symm (v i))
  have he := dualDeterminantRawAlternating_eval M lam mu (op (Over.mk (𝟙 U)))
    (fun i => (sliceSectionEquiv M U (op (Over.mk (𝟙 U)))).symm (v i))
  have hf : dualDeterminantRawAlternating M lam mu (op (Over.mk (𝟙 U)))
      (fun i => (sliceSectionEquiv M U (op (Over.mk (𝟙 U)))).symm (v i)) =
      dualDeterminantAlternating M lam mu (Over.mk (𝟙 U)) v := by
    have hv : (fun i => sliceSectionEquiv M U (op (Over.mk (𝟙 U)))
        ((sliceSectionEquiv M U (op (Over.mk (𝟙 U)))).symm (v i))) = v :=
      funext fun i => (sliceSectionEquiv M U (op (Over.mk (𝟙 U)))).apply_symm_apply (v i)
    exact he.trans (congrArg (dualDeterminantAlternating M lam mu (Over.mk (𝟙 U))) hv)
  exact hc.trans (hd.trans (hf.trans (dualDeterminantAlternating_eval M lam mu (Over.mk (𝟙 U)) v)))
end NcCubic.Geometry
