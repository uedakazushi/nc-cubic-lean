/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorRawDualIso
public import NcCubic.Geometry.ExteriorWedgeLaws
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem exteriorDualToRaw_eval_native_wedge {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (lam : Γ(dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)),U))
    (v : Fin 2 → Γ(M,U)) :
    evalAt (Scheme.Modules.exteriorPower M (2:ℤ)) lam (exteriorWedgeAlternating M U v) =
      ((((exteriorDualToRaw M).val.app (op U) lam).app (op (Over.mk (𝟙 U)))).hom
        (exteriorRawWedge M U (fun i => (siteSectionSemilinearEquiv M U).symm (v i)))) := rfl
end NcCubic.Geometry
