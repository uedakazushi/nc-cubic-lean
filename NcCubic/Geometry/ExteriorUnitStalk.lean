/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorRawDualIso
public import NcCubic.Geometry.ExteriorDualStalk
public import Mathlib.Topology.Sheaves.Sheafify
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false in
instance exteriorPresheafUnit_stalk_isIso {X : Scheme.{u}} (M : X.Modules) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map
        (exteriorPresheafUnit M))) := by
  rw [exteriorPresheafUnit_group_factor, Functor.map_comp]
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat
    (rawExteriorPresheaf M).presheaf
  infer_instance

set_option backward.isDefEq.respectTransparency false in
def nativeRawStalkEquiv {X : Scheme.{u}} (M : X.Modules) (x : X) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      ↥(TopCat.Presheaf.stalk (C := Ab)
        (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M).presheaf x) :=
  LinearEquiv.refl _ _

set_option backward.isDefEq.respectTransparency false in
def exteriorStalkEquivAlong {X : Scheme.{u}} (F Q : X.Modules) (n : ℕ) (x : X)
    (eta : PresheafOfModules.extPow (O := X.sheaf.obj) n
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) F) ⟶
      SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) Q)
    (h : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).map eta))) :
    Q.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] ⋀[X.presheaf.stalk x]^n (F.presheaf.stalk x) := by
  let Fp := SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) F
  let Qp := SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) Q
  let e : ↥(TopCat.Presheaf.stalk (C := Ab) Qp.presheaf x) ≃ₗ[X.presheaf.stalk x]
      ⋀[X.presheaf.stalk x]^n ↥(TopCat.Presheaf.stalk (C := Ab) Fp.presheaf x) :=
    PresheafOfModules.extPowStalkEquivOfStalkIso.{u} (R := X.sheaf.obj)
      (Q := Qp) Fp x n eta h
  exact (nativeRawStalkEquiv Q x).trans
    (e.trans (exteriorLinearEquiv n (nativeRawStalkEquiv F x).symm))


set_option backward.isDefEq.respectTransparency false in
/-- Exterior stalk comparison pinned to the very same global sheafification unit. -/
def unitExteriorStalkEquiv {X : Scheme.{u}} (M : X.Modules) (x : X) :
    (Scheme.Modules.exteriorPower M (2:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      ⋀[X.presheaf.stalk x]^2 (M.presheaf.stalk x) :=
  exteriorStalkEquivAlong M (Scheme.Modules.exteriorPower M (2:ℤ)) 2 x
    (exteriorPresheafUnit M) inferInstance


open Stacks.AlgebraicGeometry.ReflexiveModules
set_option backward.isDefEq.respectTransparency false in
def unitExteriorDualStalkPairingEquiv {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (x : X)
    [Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)] :
    (Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Module.Dual (X.presheaf.stalk x)
        ((Scheme.Modules.exteriorPower M (2:ℤ)).presheaf.stalk x) :=
  (unitExteriorStalkEquiv (dualSheaf M) x).trans
    ((exteriorLinearEquiv 2 (dualStalkEquiv M x)).trans
      ((LinearEquiv.ofBijective (exteriorPower.pairingDual (X.presheaf.stalk x)
        (M.presheaf.stalk x) 2) (exteriorPower.bijective_pairingDual _ _ _)).trans
          (LinearEquiv.arrowCongr (unitExteriorStalkEquiv M x).symm
            (LinearEquiv.refl (X.presheaf.stalk x) (X.presheaf.stalk x)))))

end NcCubic.Geometry
