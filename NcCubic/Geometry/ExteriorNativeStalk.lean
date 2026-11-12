/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorDualStalk
public import NcCubic.Geometry.NativeExteriorWedge
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem schemeExteriorStalkEquiv_native_wedge {X : Scheme.{u}} (M : X.Modules)
    (x : X) (U : X.Opens) (hx : x ∈ U) (v : Fin 2 → Γ(M,U)) :
    schemeExteriorStalkEquiv M 2 x
      (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower M (2:ℤ)).presheaf U x hx
        (exteriorWedgeAlternating M U v)) =
      exteriorPower.ιMulti (X.presheaf.stalk x) 2
        (fun i => TopCat.Presheaf.germ M.presheaf U x hx (v i)) := by
  rw [exteriorWedgeAlternating_homogeneousProd]
  let A := SheafOfModules.algebras (Opens.grothendieckTopology ↥X) M
  exact SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd
    A.exterior A.exteriorGenerator A.exterior_isExteriorAlgebra 2 x U hx v
end NcCubic.Geometry
