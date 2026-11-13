module
public import NcCubic.Geometry.DualIsoTransport
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u v
/-- Transport and postcompose the original dual-bicone column identity before
specializing its intermediate dual bundle to a concrete projective sum. -/
theorem dualBiconeComparison_column_post (X : Scheme.{u}) {I : Type v} [Finite I]
    {F G : I → X.Modules} (b : Bicone F) (c : Bicone G)
    (hb : b.IsBilimit) (hc : c.IsBilimit) (e : ∀ i, G i ≅ dualSheaf (X := X) (F i))
    {Q T : X.Modules} (hQ : b.pt = Q) (g : dualSheaf (X := X) Q ⟶ T)
    (i : I) (p : Q ⟶ F i) (hp : (eqToIso hQ).inv ≫ b.π i = p) :
    c.ι i ≫ ((dualIsoChangeTarget (X := X) (dualBiconeComparisonIso X b c hb hc e) hQ).hom ≫ g) =
      (e i).hom ≫ (dualMap (X := X) p ≫ g) := by
  have h := dualIsoChangeTarget_column (X := X) (dualBiconeComparisonIso X b c hb hc e)
    hQ (c.ι i) (b.π i) (e i).hom
    (dualBiconeComparisonIso_column X b c hb hc e i)
  have h' := h.trans (congrArg (fun q => (e i).hom ≫ dualMap (X := X) q) hp)
  simpa only [Category.assoc] using congrArg (fun q => q ≫ g) h'
end NcCubic.Geometry.CanonicalEulerMiddle
