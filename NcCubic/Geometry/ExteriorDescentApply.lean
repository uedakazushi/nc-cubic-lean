/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorSheafDescentUnit
public import NcCubic.Geometry.BivectorExteriorLinear
public import NcCubic.Geometry.RawExteriorWedge
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
/-- The explicit raw sectionwise wedge, before sheafification. -/
def exteriorRawWedge {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F).obj (op U)) :
    (PresheafOfModules.extPow (O := X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F)).obj (op U) :=
  PresheafExterior.wedgeSection (O := X.sheaf.obj)
    (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F) 2 (op U) v

def exteriorUnitWedge {X : Scheme.{u}} (F : X.Modules) (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F).obj (op U)) :
    (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X)
      (Scheme.Modules.exteriorPower F (2:ℤ))).obj (op U) :=
  (exteriorPresheafUnit F).app (op U) (exteriorRawWedge F U v)

theorem exteriorUnitWedge_descend {X : Scheme.{u}} (F G : X.Modules)
    (α : PresheafOfModules.extPow (O:=X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F) ⟶
      SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) G)
    (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F).obj (op U)) :
    ((moduleUnderlyingFunctor X).map (descendExteriorPresheafMorphism F G α)).app (op U)
      (exteriorUnitWedge F U v) = α.app (op U) (exteriorRawWedge F U v) :=
  presheaf_comp_apply_of_eq _ _ α (exteriorPresheafUnit_descend F G α) (op U)
    (exteriorRawWedge F U v)

theorem siteSectionSemilinearEquiv_map {X : Scheme.{u}} {M N : X.Modules}
    (g : M ⟶ N) (U : X.Opens)
    (z : (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) M).obj (op U)) :
    siteSectionSemilinearEquiv N U (((moduleUnderlyingFunctor X).map g).app (op U) z) =
      g.val.app (op U) (siteSectionSemilinearEquiv M U z) := rfl
end NcCubic.Geometry
