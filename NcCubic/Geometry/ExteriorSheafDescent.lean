module
public import NcCubic.Geometry.ProjectiveBivector
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false in
/-- Descend an actual sectionwise exterior-power morphism to the genuine exterior sheaf. -/
def descendExteriorPresheafMorphism {X : Scheme.{u}} (F G : X.Modules)
    (α : PresheafOfModules.extPow (O := X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) F) ⟶
        SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) G) :
    Scheme.Modules.exteriorPower F (2 : ℤ) ⟶ G :=
  (SheafOfModules.exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X)
    (SheafOfModules.algebras _ F) 2).hom ≫
  (PresheafOfModules.moduleSheafification (Opens.grothendieckTopology ↥X)
    (𝟙 X.sheaf.obj)).map α ≫
  (SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X) G).hom
end NcCubic.Geometry
