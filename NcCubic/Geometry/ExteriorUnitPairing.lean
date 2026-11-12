/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorUnitStalk
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
theorem unitExteriorDualStalkPairingEquiv_ιMulti {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (x : X)
    [Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)]
    (lam : Fin 2 → (dualSheaf M).presheaf.stalk x) (v : Fin 2 → M.presheaf.stalk x) :
    unitExteriorDualStalkPairingEquiv M x
      ((unitExteriorStalkEquiv (dualSheaf M) x).symm
        (exteriorPower.ιMulti (X.presheaf.stalk x) 2 lam))
      ((unitExteriorStalkEquiv M x).symm
        (exteriorPower.ιMulti (X.presheaf.stalk x) 2 v)) =
      Matrix.det (n := Fin 2) (Matrix.of (fun i j => dualStalkEquiv M x (lam j) (v i))) := by
  simp only [unitExteriorDualStalkPairingEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.arrowCongr_apply, LinearEquiv.refl_apply,
    LinearEquiv.symm_symm]
  change exteriorPower.pairingDual (X.presheaf.stalk x) (M.presheaf.stalk x) 2
    (exteriorPower.map 2 (dualStalkEquiv M x).toLinearMap
      (exteriorPower.ιMulti (X.presheaf.stalk x) 2 lam))
    (exteriorPower.ιMulti (X.presheaf.stalk x) 2 v) = _
  rw [exteriorPower.map_apply_ιMulti]
  exact exteriorPower.pairingDual_ιMulti_ιMulti (R := X.presheaf.stalk x)
    (fun i => dualStalkEquiv M x (lam i)) v

set_option backward.isDefEq.respectTransparency false in
def unitExteriorDualStalkEquiv {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation]
    [(Scheme.Modules.exteriorPower M (2:ℤ)).IsFinitePresentation] (x : X)
    [Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)] :
    (Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ))).presheaf.stalk x :=
  (unitExteriorDualStalkPairingEquiv M x).trans
    (dualStalkEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) x).symm

set_option backward.isDefEq.respectTransparency false in
def unitExteriorDualStalkEquivOfFiniteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M]
    (x : X) :
    (Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ))).presheaf.stalk x := by
  letI : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u} M :=
    stackFiniteLocallyFree_of_finiteLocallyFree M hM
  letI : M.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation M
  letI : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Modules.exteriorPower M (2:ℤ)) := exterior_finiteLocallyFree M 2 inferInstance
  letI : (Scheme.Modules.exteriorPower M (2:ℤ)).IsFinitePresentation :=
    Stacks.FiniteLocallyFree.isFinitePresentation (Scheme.Modules.exteriorPower M (2:ℤ))
  have hfree := Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree M x
  letI : Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) := hfree.1
  letI : Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x) := hfree.2
  exact unitExteriorDualStalkEquiv M x

end NcCubic.Geometry
