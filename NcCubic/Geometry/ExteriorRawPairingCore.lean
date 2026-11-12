/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorRawDual
public import NcCubic.Geometry.ExteriorDualLocalPairing
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
variable {C : Type u} [Category.{u} C] (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (P Q : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)) (U : C) (n : ℕ)
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
def overExteriorFunctional
    (d : PresheafOfModules.extPow (O := (Over.forget U).op ⋙ O) n
        ((restrFun O U).obj P) ⟶ (restrFun O U).obj Q) :
    (restrFun O U).obj (PresheafOfModules.extPow (O := O) n P) ⟶
      (restrFun O U).obj Q :=
  (PresheafOfModules.extPowOverIso (O := O) U n P).hom ≫ d


set_option backward.isDefEq.respectTransparency false in
theorem sliceRawModule_eq {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (restrFun X.sheaf.obj U).obj (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M) =
      SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U) (SliceModule M U) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sliceRawUnit_eq (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U) (SliceUnit X U) =
    (restrFun X.sheaf.obj U).obj (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (SheafOfModules.unit X.ringCatSheaf)) := by rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
def localRawExteriorPairing {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) : Γ(exteriorRawDualSheaf M,U) :=
  overExteriorFunctional X.sheaf.obj
    (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M)
    (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (SheafOfModules.unit X.ringCatSheaf)) U 2
      (eqToHom (congrArg (fun F => PresheafOfModules.extPow
          (O := (X.sheaf.over U).obj) 2 F) (sliceRawModule_eq M U)) ≫
        localDeterminantPresheaf M lam mu ≫ eqToHom (sliceRawUnit_eq X U))



set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
theorem localRawExteriorPairing_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ≤ U) (lam mu : Γ(dualSheaf M,U)) :
    (exteriorRawDualSheaf M).presheaf.map (homOfLE h).op (localRawExteriorPairing M lam mu) =
      localRawExteriorPairing M ((dualSheaf M).presheaf.map (homOfLE h).op lam)
        ((dualSheaf M).presheaf.map (homOfLE h).op mu) := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (localDeterminantPresheaf M lam mu).app
      (op (Over.mk (Z.unop.hom ≫ homOfLE h))) z =
    (localDeterminantPresheaf M ((dualSheaf M).presheaf.map (homOfLE h).op lam)
      ((dualSheaf M).presheaf.map (homOfLE h).op mu)).app Z z
  rfl
end NcCubic.Geometry
