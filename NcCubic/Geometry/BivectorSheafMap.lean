module
public import NcCubic.Geometry.BivectorExteriorLinear
public import NcCubic.Geometry.PresheafExteriorDesc
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false in
/-- Canonical actual contraction from the sectionwise exterior presheaf of tangent fields. -/
def exteriorContractionPresheaf {X S : Scheme.{u}} (f : X ⟶ S) :
    PresheafOfModules.extPow (O := X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (tangentSheaf f)) ⟶
      SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (tangentContractionSheaf f) :=
  PresheafExterior.desc (O := X.sheaf.obj)
    (fun U => wedgeContractionRawAlternating f U.unop)
    (fun h v => wedgeContractionRawAlternating_natural f h.unop v)

end NcCubic.Geometry
