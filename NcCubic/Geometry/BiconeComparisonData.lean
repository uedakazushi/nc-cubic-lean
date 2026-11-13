module
public import NcCubic.Geometry.BiconePostColumns
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u v
/-- A canonical comparison and its postcomposed coordinate laws, kept together
so concrete applications share the same morphism term. -/
structure BiconeComparisonData (X : Scheme.{u}) {I : Type v}
    (F G : I → X.Modules) (c : Bicone G) (Q T : X.Modules)
    (e : ∀ i, G i ≅ dualSheaf (X := X) (F i))
    (p : ∀ i, Q ⟶ F i) (g : dualSheaf (X := X) Q ⟶ T) where
  iso : c.pt ≅ dualSheaf (X := X) Q
  column : ∀ i, c.ι i ≫ (iso.hom ≫ g) =
    (e i).hom ≫ (dualMap (X := X) (p i) ≫ g)

/-- Construct the package from the ORIGINAL negative bicone, native positive
bicone, and literal pointwise dualities. No map or column law is assumed. -/
def biconeComparisonData (X : Scheme.{u}) {I : Type v} [Finite I]
    {F G : I → X.Modules} (b : Bicone F) (c : Bicone G)
    (hb : b.IsBilimit) (hc : c.IsBilimit)
    (e : ∀ i, G i ≅ dualSheaf (X := X) (F i))
    {Q T : X.Modules} (hQ : b.pt = Q) (p : ∀ i, Q ⟶ F i)
    (hp : ∀ i, (eqToIso hQ).inv ≫ b.π i = p i)
    (g : dualSheaf (X := X) Q ⟶ T) : BiconeComparisonData X F G c Q T e p g where
  iso := dualIsoChangeTarget (X := X) (dualBiconeComparisonIso X b c hb hc e) hQ
  column i := dualBiconeComparison_column_post X b c hb hc e hQ g i (p i) (hp i)
end NcCubic.Geometry.CanonicalEulerMiddle
