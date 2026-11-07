/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorDescentApply
public import NcCubic.Geometry.BivectorSheafDesc
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
/-- The actual exterior section determined by two local tangent fields,
read through the explicit raw exterior sheafification unit. -/
def tangentWedgeSection (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp := X.sheaf)
      (Opens.grothendieckTopology ↥X) (tangentSheaf f)).obj (op U)) : Γ(bivectorSheaf f,U) :=
  siteSectionSemilinearEquiv (bivectorSheaf f) U (exteriorUnitWedge (tangentSheaf f) U v)

theorem bivectorContraction_tangentWedgeSection (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp := X.sheaf)
      (Opens.grothendieckTopology ↥X) (tangentSheaf f)).obj (op U)) :
    (bivectorContraction f).val.app (op U) (tangentWedgeSection f U v) =
      wedgeContractionLocal f U (fun i => siteSectionSemilinearEquiv (tangentSheaf f) U (v i)) := by
  let α := exteriorContractionPresheaf f
  have hα : α.app (op U) (exteriorRawWedge (tangentSheaf f) U v) =
      wedgeContractionRawAlternating f U v :=
    PresheafExterior.desc_wedgeSection (O := X.sheaf.obj)
      (SheafOfModules.valPresheaf (Osharp := X.sheaf)
        (Opens.grothendieckTopology ↥X) (tangentSheaf f)) 2
      (fun V => wedgeContractionRawAlternating f V.unop)
      (fun h v => wedgeContractionRawAlternating_natural f h.unop v) (op U) v
  have hraw := (exteriorUnitWedge_descend (tangentSheaf f) (tangentContractionSheaf f) α U v).trans hα
  have hsite := siteSectionSemilinearEquiv_map (bivectorContraction f) U
    (exteriorUnitWedge (tangentSheaf f) U v)
  exact hsite.symm.trans ((congrArg (siteSectionSemilinearEquiv (tangentContractionSheaf f) U)
    hraw).trans (wedgeContractionRawAlternating_eval f U v))
end NcCubic.Geometry
