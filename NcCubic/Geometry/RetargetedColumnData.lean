module
public import NcCubic.Geometry.BiconeComparisonData
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u v

/-- An isomorphism and its column laws with the source and target column
families frozen in the interface. -/
structure ColumnComparisonData (X : Scheme.{u}) {I : Type v}
    (G : I → X.Modules) (P Q T : X.Modules)
    (a : ∀ i, G i ⟶ P) (vcol : ∀ i, G i ⟶ T)
    (g : dualSheaf (X := X) Q ⟶ T) where
  iso : P ≅ dualSheaf (X := X) Q
  column : ∀ i, a i ≫ (iso.hom ≫ g) = vcol i

/-- Keep the SAME isomorphism and retarget only the displayed column
endpoints. Both endpoint equalities are proved before concrete specialization. -/
def BiconeComparisonData.retargetColumns {X : Scheme.{u}} {I : Type v}
    {F G : I → X.Modules} {c : Bicone G} {Q T : X.Modules}
    {e : ∀ i, G i ≅ dualSheaf (X := X) (F i)}
    {p : ∀ i, Q ⟶ F i} {g : dualSheaf (X := X) Q ⟶ T}
    (d : BiconeComparisonData X F G c Q T e p g)
    (a : ∀ i, G i ⟶ c.pt) (vcol : ∀ i, G i ⟶ T)
    (ha : ∀ i, c.ι i = a i)
    (hv : ∀ i, (e i).hom ≫ (dualMap (X := X) (p i) ≫ g) = vcol i) :
    ColumnComparisonData X G c.pt Q T a vcol g where
  iso := d.iso
  column i := by
    calc
      a i ≫ (d.iso.hom ≫ g) = c.ι i ≫ (d.iso.hom ≫ g) :=
        congrArg (fun f => f ≫ (d.iso.hom ≫ g)) (ha i).symm
      _ = (e i).hom ≫ (dualMap (X := X) (p i) ≫ g) := d.column i
      _ = vcol i := hv i

end NcCubic.Geometry.CanonicalEulerMiddle
