module
public import NcCubic.Geometry.BivectorSheafMap
public import NcCubic.Geometry.ContractionEvaluation
public import NcCubic.Geometry.ExteriorSheafDescent
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism from actual tangent bivectors to actual contraction maps. -/
def bivectorContraction {X S : Scheme.{u}} (f : X ⟶ S) :
    bivectorSheaf f ⟶ tangentContractionSheaf f :=
  descendExteriorPresheafMorphism (tangentSheaf f) (tangentContractionSheaf f)
    (exteriorContractionPresheaf f)
/-- The operation induced by an actual global tangent bivector. -/
def algebraicBivectorBracket {X S : Scheme.{u}} (f : X ⟶ S)
    (π : AlgebraicBivector f) : StructureSheafBracket X :=
  contractionGlobalBracket f ((bivectorContraction f).val.app (op ⊤) π)
end NcCubic.Geometry
