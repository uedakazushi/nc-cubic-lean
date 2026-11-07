/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorSheafDescentUnit
public import NcCubic.Geometry.ExteriorSiteDescent
public import NcCubic.Geometry.ExteriorDualLocalPairing
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceSheafification
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.PresheafOfModules.InternalHom
universe u

def rawExteriorPresheaf {X : Scheme.{u}} (M : X.Modules) :=
  PresheafOfModules.extPow (O := X.sheaf.obj) 2
    (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M)

set_option backward.isDefEq.respectTransparency false in
/-- Local raw exterior functionals form a genuine sheaf because their target is the structure sheaf. -/
def exteriorRawDualSheaf {X : Scheme.{u}} (M : X.Modules) : X.Modules where
  val := internalHom X.sheaf.obj (rawExteriorPresheaf M)
    (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (SheafOfModules.unit X.ringCatSheaf))
  isSheaf := internalHom_isSheaf X.sheaf.obj (rawExteriorPresheaf M) _
    (SheafOfModules.unit X.ringCatSheaf).isSheaf

set_option backward.isDefEq.respectTransparency false in
/-- Canonical precomposition by the actual exterior sheafification unit. -/
def exteriorDualToRaw {X : Scheme.{u}} (M : X.Modules) :
    dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)) ⟶ exteriorRawDualSheaf M where
  val := internalHomMapLeft X.sheaf.obj (exteriorPresheafUnit M)


set_option backward.isDefEq.respectTransparency false in
def exteriorUnitGroupIso {X : Scheme.{u}} (M : X.Modules) :=
  (PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).mapIso
    ((moduleUnderlyingFunctor X).mapIso
      (SheafOfModules.exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X)
        (SheafOfModules.algebras _ M) 2).symm)

set_option backward.isDefEq.respectTransparency false in
theorem exteriorPresheafUnit_group_factor {X : Scheme.{u}} (M : X.Modules) :
    (PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
      (exteriorPresheafUnit M) =
    CategoryTheory.toSheafify (Opens.grothendieckTopology ↥X) (rawExteriorPresheaf M).presheaf ≫
      (exteriorUnitGroupIso M).hom := rfl

set_option backward.isDefEq.respectTransparency false in
instance exteriorPresheafUnit_locallyInjective {X : Scheme.{u}} (M : X.Modules) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
        (exteriorPresheafUnit M)) := by
  let J := Opens.grothendieckTopology ↥X
  let eta := CategoryTheory.toSheafify J (rawExteriorPresheaf M).presheaf
  let beta := (exteriorUnitGroupIso M).hom
  let : Presheaf.IsLocallyInjective J eta := (J.W_toSheafify _).isLocallyInjective
  let : Presheaf.IsLocallyInjective J beta :=
    Presheaf.isLocallyInjective_of_injective J beta
      (fun V => ((exteriorUnitGroupIso M).app V).addCommGroupIsoToAddEquiv.injective)
  rw [exteriorPresheafUnit_group_factor]
  exact Presheaf.isLocallyInjective_comp J eta beta

set_option backward.isDefEq.respectTransparency false in
instance exteriorPresheafUnit_locallySurjective {X : Scheme.{u}} (M : X.Modules) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥X)
      ((PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
        (exteriorPresheafUnit M)) := by
  let J := Opens.grothendieckTopology ↥X
  let eta := CategoryTheory.toSheafify J (rawExteriorPresheaf M).presheaf
  let beta := (exteriorUnitGroupIso M).hom
  let : Presheaf.IsLocallySurjective J eta := (J.W_toSheafify _).isLocallySurjective
  let : Presheaf.IsLocallySurjective J beta :=
    Presheaf.isLocallySurjective_of_surjective J beta
      (fun V => ((exteriorUnitGroupIso M).app V).addCommGroupIsoToAddEquiv.surjective)
  rw [exteriorPresheafUnit_group_factor]
  exact Presheaf.isLocallySurjective_comp J eta beta

set_option backward.isDefEq.respectTransparency false in
/-- The globally chosen exterior unit restricted to a slice, retaining its components. -/
def restrictedExteriorUnit {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (restrFun X.sheaf.obj U).obj (rawExteriorPresheaf M) ⟶
      SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
        (SliceModule (Scheme.Modules.exteriorPower M (2:ℤ)) U) where
  app Z := (exteriorPresheafUnit M).app (op Z.unop.left)
  naturality k := (exteriorPresheafUnit M).naturality k.unop.left.op

set_option backward.isDefEq.respectTransparency false in
theorem restrictedExteriorUnit_group {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (PresheafOfModules.toPresheaf (((X.sheaf.over U).obj) ⋙ forget₂ CommRingCat RingCat)).map
        (restrictedExteriorUnit M U) =
      Functor.whiskerLeft (Over.forget U).op
        ((PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
          (exteriorPresheafUnit M)) := rfl


end NcCubic.Geometry
