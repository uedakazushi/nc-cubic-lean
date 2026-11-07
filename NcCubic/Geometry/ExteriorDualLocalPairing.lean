/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorSiteDescent
public import NcCubic.Geometry.ExteriorRestriction
public import NcCubic.Geometry.BivectorExteriorLinear
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
abbrev SliceModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    SheafOfModules (Sheaf.toRingCat ((Opens.grothendieckTopology ↥X).over U) (X.sheaf.over U)) :=
  M.over U
abbrev SliceUnit (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules (Sheaf.toRingCat ((Opens.grothendieckTopology ↥X).over U) (X.sheaf.over U)) :=
  SheafOfModules.unit _

def sliceRingEquiv (X : Scheme.{u}) (U : X.Opens) (Z : (Over U)ᵒᵖ) :
    ((X.sheaf.over U).obj ⋙ forget₂ CommRingCat RingCat).obj Z ≃+* Γ(X,Z.unop.left) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
instance sliceRingEquiv_invPair (X : Scheme.{u}) (U : X.Opens) (Z : (Over U)ᵒᵖ) :
    RingHomInvPair (RingHomClass.toRingHom (sliceRingEquiv X U Z))
      (RingHomClass.toRingHom (sliceRingEquiv X U Z).symm) where
  comp_eq := by ext; rfl
  comp_eq₂ := by ext; rfl
instance sliceRingEquiv_invPair_symm (X : Scheme.{u}) (U : X.Opens) (Z : (Over U)ᵒᵖ) :
    RingHomInvPair (RingHomClass.toRingHom (sliceRingEquiv X U Z).symm)
      (RingHomClass.toRingHom (sliceRingEquiv X U Z)) where
  comp_eq := by ext; rfl
  comp_eq₂ := by ext; rfl
set_option backward.isDefEq.respectTransparency false in
def sliceSectionEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (Z : (Over U)ᵒᵖ) :
    LinearEquiv (RingHomClass.toRingHom (sliceRingEquiv X U Z))
      (σ' := RingHomClass.toRingHom (sliceRingEquiv X U Z).symm)
      ((SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
        (SliceModule M U)).obj Z) Γ(M,Z.unop.left) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
set_option backward.isDefEq.respectTransparency false in
def sliceUnitEquiv (X : Scheme.{u}) (U : X.Opens) (Z : (Over U)ᵒᵖ) :
    LinearEquiv (RingHomClass.toRingHom (sliceRingEquiv X U Z))
      (σ' := RingHomClass.toRingHom (sliceRingEquiv X U Z).symm)
      ((SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
        (SliceUnit X U)).obj Z) Γ(X,Z.unop.left) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def dualLocalEvaluation {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam : Γ(dualSheaf M,U)) (Z : Over U) : Γ(M,Z.left) →ₗ[Γ(X,Z.left)] Γ(X,Z.left) :=
  (lam.app (op Z)).hom

def dualDeterminantAlternating {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) (Z : Over U) :
    AlternatingMap Γ(X,Z.left) Γ(M,Z.left) Γ(X,Z.left) (Fin 2) :=
  (exteriorPower.pairingDual Γ(X,Z.left) Γ(M,Z.left) 2
    (exteriorPower.ιMulti Γ(X,Z.left) 2
      ![dualLocalEvaluation M lam Z,dualLocalEvaluation M mu Z])).compAlternatingMap
    (exteriorPower.ιMulti Γ(X,Z.left) 2)

theorem dualDeterminantAlternating_eval {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) (Z : Over U) (v : Fin 2 → Γ(M,Z.left)) :
    dualDeterminantAlternating M lam mu Z v =
      dualPairing M lam Z (v 0)*dualPairing M mu Z (v 1) -
        dualPairing M mu Z (v 0)*dualPairing M lam Z (v 1) := by
  simp only [dualDeterminantAlternating,LinearMap.compAlternatingMap_apply,
    exteriorPower.pairingDual_ιMulti_ιMulti,Matrix.det_fin_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl
set_option backward.isDefEq.respectTransparency false in
def dualDeterminantRawAlternating {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) (Z : (Over U)ᵒᵖ) :
    AlternatingMap (((X.sheaf.over U).obj ⋙ forget₂ CommRingCat RingCat).obj Z)
      ((SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
        (SliceModule M U)).obj Z)
      ((SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
        (SliceUnit X U)).obj Z) (Fin 2) :=
  alternatingSemilinearTransport (dualDeterminantAlternating M lam mu Z.unop)
    (sliceSectionEquiv M U Z).toLinearMap (sliceUnitEquiv X U Z).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
theorem dualDeterminantRawAlternating_natural {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) {Z Z' : (Over U)ᵒᵖ} (k : Z ⟶ Z')
    (v : Fin 2 → (SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
      (SliceModule M U)).obj Z) :
    (SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U) (SliceUnit X U)).map k
        (dualDeterminantRawAlternating M lam mu Z v) =
      dualDeterminantRawAlternating M lam mu Z'
        (fun i => (SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
          (SliceModule M U)).map k (v i)) := by
  apply (sliceUnitEquiv X U Z').injective
  change X.presheaf.map k.unop.left.op (dualDeterminantAlternating M lam mu Z.unop
      (fun i => sliceSectionEquiv M U Z (v i))) =
    dualDeterminantAlternating M lam mu Z'.unop
      (fun i => M.presheaf.map k.unop.left.op (sliceSectionEquiv M U Z (v i)))
  simp only [dualDeterminantAlternating_eval,map_sub,map_mul,
    dualPairing_naturality]


set_option backward.isDefEq.respectTransparency false in
theorem dualDeterminantRawAlternating_eval {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) (Z : (Over U)ᵒᵖ)
    (v : Fin 2 → (SheafOfModules.valPresheaf ((Opens.grothendieckTopology ↥X).over U)
      (SliceModule M U)).obj Z) :
    sliceUnitEquiv X U Z (dualDeterminantRawAlternating M lam mu Z v) =
      dualDeterminantAlternating M lam mu Z.unop (fun i => sliceSectionEquiv M U Z (v i)) :=
  (sliceUnitEquiv X U Z).apply_symm_apply _

theorem dualDeterminantRawAlternating_add_left {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam lam' mu : Γ(dualSheaf M,U)) (Z : (Over U)ᵒᵖ) :
    dualDeterminantRawAlternating M (lam+lam') mu Z =
      dualDeterminantRawAlternating M lam mu Z + dualDeterminantRawAlternating M lam' mu Z := by
  apply AlternatingMap.ext
  intro v
  apply (sliceUnitEquiv X U Z).injective
  simp only [add_apply,map_add,dualDeterminantRawAlternating_eval,
    dualDeterminantAlternating_eval]
  have hh (a : Γ(M,Z.unop.left)) : dualPairing M (lam+lam') Z.unop a =
      dualPairing M lam Z.unop a+dualPairing M lam' Z.unop a := rfl
  simp only [hh]
  ring

theorem dualDeterminantRawAlternating_add_right {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu mu' : Γ(dualSheaf M,U)) (Z : (Over U)ᵒᵖ) :
    dualDeterminantRawAlternating M lam (mu+mu') Z =
      dualDeterminantRawAlternating M lam mu Z + dualDeterminantRawAlternating M lam mu' Z := by
  apply AlternatingMap.ext
  intro v
  apply (sliceUnitEquiv X U Z).injective
  simp only [add_apply,map_add,dualDeterminantRawAlternating_eval,
    dualDeterminantAlternating_eval]
  have hh (a : Γ(M,Z.unop.left)) : dualPairing M (mu+mu') Z.unop a =
      dualPairing M mu Z.unop a+dualPairing M mu' Z.unop a := rfl
  simp only [hh]
  ring

theorem dualDeterminantRawAlternating_self {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam : Γ(dualSheaf M,U)) (Z : (Over U)ᵒᵖ) :
    dualDeterminantRawAlternating M lam lam Z=0 := by
  apply AlternatingMap.ext
  intro v
  apply (sliceUnitEquiv X U Z).injective
  simp only [zero_apply,map_zero,dualDeterminantRawAlternating_eval,
    dualDeterminantAlternating_eval,sub_self]

set_option backward.isDefEq.respectTransparency false in
def localDeterminantPresheaf {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) :=
  PresheafExterior.desc (fun Z => dualDeterminantRawAlternating M lam mu Z)
    (fun k v => dualDeterminantRawAlternating_natural M lam mu k v)

set_option backward.isDefEq.respectTransparency false in
/-- Two actual local functionals define an actual functional on the exterior sheaf. -/
def localExteriorDualPairing {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu : Γ(dualSheaf M,U)) :
    Γ(dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)),U) :=
  ((exteriorRestrictionIso M U 2).hom ≫
    exteriorSiteHomEquiv ((Opens.grothendieckTopology ↥X).over U)
      (SliceModule M U) (SliceUnit X U) 2 (localDeterminantPresheaf M lam mu)).val
end NcCubic.Geometry
