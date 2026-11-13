module
public import NcCubic.Geometry.BiconeDualColumns
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
/-- Change the two vertices before specializing the dual sheaf to concrete sums. -/
def dualIsoChangeVertices {X : Scheme.{u}} {P Q P' Q' : X.Modules}
    (e : P ≅ dualSheaf (X := X) Q) (hP : P = P') (hQ : Q = Q') : P' ≅ dualSheaf (X := X) Q' :=
  (eqToIso hP).symm ≪≫ e ≪≫ (dualSheafIsoOfIso (X := X) (eqToIso hQ)).symm

theorem dualIsoChangeVertices_column {X : Scheme.{u}} {P Q P' Q' A B : X.Modules}
    (e : P ≅ dualSheaf (X := X) Q) (hP : P = P') (hQ : Q = Q')
    (i : A ⟶ P) (p : Q ⟶ B) (k : A ⟶ dualSheaf (X := X) B)
    (h : i ≫ e.hom = k ≫ dualMap (X := X) p) :
    (i ≫ (eqToIso hP).hom) ≫ (dualIsoChangeVertices (X := X) e hP hQ).hom =
      k ≫ dualMap (X := X) ((eqToIso hQ).inv ≫ p) := by
  subst P'
  subst Q'
  simpa [dualIsoChangeVertices, dualSheafIsoOfIso] using h

/-- Transport only the negative vertex, retaining the literal positive bicone. -/
def dualIsoChangeTarget {X : Scheme.{u}} {P Q Q' : X.Modules}
    (e : P ≅ dualSheaf (X := X) Q) (hQ : Q = Q') : P ≅ dualSheaf (X := X) Q' :=
  e ≪≫ (dualSheafIsoOfIso (X := X) (eqToIso hQ)).symm

theorem dualIsoChangeTarget_column {X : Scheme.{u}} {P Q Q' A B : X.Modules}
    (e : P ≅ dualSheaf (X := X) Q) (hQ : Q = Q')
    (i : A ⟶ P) (p : Q ⟶ B) (k : A ⟶ dualSheaf (X := X) B)
    (h : i ≫ e.hom = k ≫ dualMap (X := X) p) :
    i ≫ (dualIsoChangeTarget (X := X) e hQ).hom =
      k ≫ dualMap (X := X) ((eqToIso hQ).inv ≫ p) := by
  subst Q'
  simpa [dualIsoChangeTarget, dualSheafIsoOfIso] using h

end NcCubic.Geometry.CanonicalEulerMiddle
