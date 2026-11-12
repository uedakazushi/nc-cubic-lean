/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorRawDual
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
instance restrictedExteriorUnit_locallyInjective {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Presheaf.IsLocallyInjective ((Opens.grothendieckTopology ↥X).over U)
      ((PresheafOfModules.toPresheaf (((X.sheaf.over U).obj) ⋙ forget₂ CommRingCat RingCat)).map
        (restrictedExteriorUnit M U)) := by
  rw [restrictedExteriorUnit_group]
  exact Presheaf.isLocallyInjective_whisker ((Opens.grothendieckTopology ↥X).over U)
    (Opens.grothendieckTopology ↥X) (Over.forget U) _

set_option backward.isDefEq.respectTransparency false in
instance restrictedExteriorUnit_locallySurjective {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Presheaf.IsLocallySurjective ((Opens.grothendieckTopology ↥X).over U)
      ((PresheafOfModules.toPresheaf (((X.sheaf.over U).obj) ⋙ forget₂ CommRingCat RingCat)).map
        (restrictedExteriorUnit M U)) := by
  rw [restrictedExteriorUnit_group]
  exact Presheaf.isLocallySurjective_whisker ((Opens.grothendieckTopology ↥X).over U)
    (Opens.grothendieckTopology ↥X) (Over.forget U) _


set_option backward.isDefEq.respectTransparency false in
def exteriorDualRawEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)),U) ≃ Γ(exteriorRawDualSheaf M,U) := by
  letI : PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology ↥X).over U)
      (restrictedExteriorUnit M U) := restrictedExteriorUnit_locallySurjective M U
  letI : PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology ↥X).over U)
      (restrictedExteriorUnit M U) := restrictedExteriorUnit_locallyInjective M U
  exact PresheafOfModules.homEquivOfIsLocallyBijective
    (restrictedExteriorUnit M U) (SliceUnit X U).isSheaf

set_option backward.isDefEq.respectTransparency false in
theorem exteriorDualRawEquiv_apply {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (t : Γ(dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)),U)) :
    exteriorDualRawEquiv M U t = (exteriorDualToRaw M).app U t := rfl

set_option backward.isDefEq.respectTransparency false in
theorem exteriorDualToRaw_app_bijective {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Function.Bijective ((exteriorDualToRaw M).app U) := by
  have he : (exteriorDualRawEquiv M U : _ → _) = ((exteriorDualToRaw M).app U : _ → _) :=
    funext (exteriorDualRawEquiv_apply M U)
  rw [← he]
  exact (exteriorDualRawEquiv M U).bijective

set_option backward.isDefEq.respectTransparency false in
theorem sheafMap_isIso_of_app_bijective {X : Scheme.{u}} {F G : X.Modules}
    (f : F ⟶ G) (hf : ∀ U : X.Opens, Function.Bijective (f.app U)) : IsIso f := by
  let e := PresheafOfModules.isoMk
    (fun U => (LinearEquiv.ofBijective (f.val.app U).hom (hf U.unop)).toModuleIso)
    (fun {_ _} k => f.val.naturality k)
  have : (SheafOfModules.forget X.ringCatSheaf).ReflectsIsomorphisms :=
    (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).reflectsIsomorphisms
  have : IsIso ((SheafOfModules.forget X.ringCatSheaf).map f) :=
    show IsIso e.hom from inferInstance
  exact isIso_of_reflects_iso f (SheafOfModules.forget X.ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
instance exteriorDualToRaw_isIso {X : Scheme.{u}} (M : X.Modules) :
    IsIso (exteriorDualToRaw M) :=
  sheafMap_isIso_of_app_bijective (exteriorDualToRaw M) (exteriorDualToRaw_app_bijective M)

end NcCubic.Geometry
