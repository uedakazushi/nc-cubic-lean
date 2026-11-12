module
public import NcCubic.Geometry.BiconeDualColumns
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
/-- Change the two vertices before specializing the dual sheaf to concrete sums. -/
def dualIsoChangeVertices {X : Scheme.{u}} {P Q P' Q' : X.Modules}
    (e : P ≅ dualSheaf Q) (hP : P = P') (hQ : Q = Q') : P' ≅ dualSheaf Q' :=
  (eqToIso hP).symm ≪≫ e ≪≫ (dualSheafIsoOfIso (eqToIso hQ)).symm

theorem dualIsoChangeVertices_column {X : Scheme.{u}} {P Q P' Q' A B : X.Modules}
    (e : P ≅ dualSheaf Q) (hP : P = P') (hQ : Q = Q')
    (i : A ⟶ P) (p : Q ⟶ B) (k : A ⟶ dualSheaf B)
    (h : i ≫ e.hom = k ≫ dualMap p) :
    (i ≫ (eqToIso hP).hom) ≫ (dualIsoChangeVertices e hP hQ).hom =
      k ≫ dualMap ((eqToIso hQ).inv ≫ p) := by
  subst P'
  subst Q'
  simpa [dualIsoChangeVertices, dualSheafIsoOfIso] using h

/-- Transport only the negative vertex, retaining the literal positive bicone. -/
def dualIsoChangeTarget {X : Scheme.{u}} {P Q Q' : X.Modules}
    (e : P ≅ dualSheaf Q) (hQ : Q = Q') : P ≅ dualSheaf Q' :=
  e ≪≫ (dualSheafIsoOfIso (eqToIso hQ)).symm

theorem dualIsoChangeTarget_column {X : Scheme.{u}} {P Q Q' A B : X.Modules}
    (e : P ≅ dualSheaf Q) (hQ : Q = Q')
    (i : A ⟶ P) (p : Q ⟶ B) (k : A ⟶ dualSheaf B)
    (h : i ≫ e.hom = k ≫ dualMap p) :
    i ≫ (dualIsoChangeTarget e hQ).hom =
      k ≫ dualMap ((eqToIso hQ).inv ≫ p) := by
  subst Q'
  simpa [dualIsoChangeTarget, dualSheafIsoOfIso] using h

end NcCubic.Geometry.CanonicalEulerMiddle
