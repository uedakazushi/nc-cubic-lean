module
public import NcCubic.Geometry.BiconeComparisonData
public import NcCubic.Geometry.TangentSheaf
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u v

/-- Evaluate the proved column identity on a section and a function. This is
an equality in the scalar structure sheaf, not a fresh equality of tangent maps. -/
theorem BiconeComparisonData.column_scalar_action
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    {F G : I → X.Modules} {c : Bicone G} {Q : X.Modules}
    {e : ∀ i, G i ≅ dualSheaf (X := X) (F i)}
    {p : ∀ i, Q ⟶ F i}
    {g : dualSheaf (X := X) Q ⟶ tangentSheaf (X := X) (S := S) f}
    (d : BiconeComparisonData X F G c Q (tangentSheaf (X := X) (S := S) f) e p g)
    (U : X.Opens) (i : I) (s : (G i).val.obj (op U)) (a : Γ(X,U)) :
    tangentSectionDerivation (X := X) (S := S) f U
      ((d.iso.hom ≫ g).val.app (op U) ((c.ι i).val.app (op U) s)) a =
    tangentSectionDerivation (X := X) (S := S) f U
      ((dualMap (X := X) (p i) ≫ g).val.app (op U) ((e i).hom.val.app (op U) s)) a := by
  change tangentSectionDerivation (X := X) (S := S) f U
      ((c.ι i ≫ (d.iso.hom ≫ g)).val.app (op U) s) a =
    tangentSectionDerivation (X := X) (S := S) f U
      (((e i).hom ≫ (dualMap (X := X) (p i) ≫ g)).val.app (op U) s) a
  exact congrArg (fun m : G i ⟶ tangentSheaf (X := X) (S := S) f =>
    tangentSectionDerivation (X := X) (S := S) f U (m.val.app (op U) s) a) (d.column i)

/-- A generic source-column coherence may be used before evaluating. -/
theorem BiconeComparisonData.column_scalar_action_source
    {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    {F G : I → X.Modules} {c : Bicone G} {Q : X.Modules}
    {e : ∀ i, G i ≅ dualSheaf (X := X) (F i)}
    {p : ∀ i, Q ⟶ F i}
    {g : dualSheaf (X := X) Q ⟶ tangentSheaf (X := X) (S := S) f}
    (d : BiconeComparisonData X F G c Q (tangentSheaf (X := X) (S := S) f) e p g)
    (U : X.Opens) (i : I) (asource : G i ⟶ c.pt) (ha : c.ι i = asource)
    (s : (G i).val.obj (op U)) (a : Γ(X,U)) :
    tangentSectionDerivation (X := X) (S := S) f U
      ((d.iso.hom ≫ g).val.app (op U) (asource.val.app (op U) s)) a =
    tangentSectionDerivation (X := X) (S := S) f U
      ((dualMap (X := X) (p i) ≫ g).val.app (op U) ((e i).hom.val.app (op U) s)) a := by
  rw [← ha]
  exact d.column_scalar_action (X := X) (S := S) f U i s a
end NcCubic.Geometry.CanonicalEulerMiddle
