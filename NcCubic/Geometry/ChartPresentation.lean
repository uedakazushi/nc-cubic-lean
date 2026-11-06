/- A concrete one-equation presentation of the affine hypersurface chart.
The relation and canonical quotient generators are computed, rather than assumed. -/
module
public import NcCubic.Geometry.AffineChart
public import Mathlib.RingTheory.Extension.Presentation.Submersive
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.AffineChart
open MvPolynomial
variable {R σ : Type*} [CommRing R]
theorem relationIdealEq (F : MvPolynomial (σ ⊕ Unit) R) :
    Ideal.span (Set.range (fun _ : Unit => dehomogenize F)) =
      Ideal.span ({dehomogenize F} : Set (MvPolynomial σ R)) := by
  simp

/-- The actual polynomial quotient has one relation, its dehomogenized equation. -/
def presentation (F : MvPolynomial (σ ⊕ Unit) R) :
    Algebra.Presentation R (CoordinateRing F) σ Unit :=
  (Algebra.Presentation.naive (v := fun _ : Unit => dehomogenize F)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq (R₁ := R) (relationIdealEq F))

/-- The presentation relation is the chart equation itself. -/
theorem presentation_relation (F : MvPolynomial (σ ⊕ Unit) R) (u : Unit) :
    (presentation F).relation u = dehomogenize F := by
  rfl

/-- Presentation generators are the canonical quotient coordinate functions. -/
theorem presentation_val (F : MvPolynomial (σ ⊕ Unit) R) (a : σ) :
    (presentation F).val a = Ideal.Quotient.mk _ (X a) := by
  simp [presentation]
/-- Choosing an affine variable selects the one-by-one Jacobian minor. -/
def preSubmersivePresentation (F : MvPolynomial (σ ⊕ Unit) R) (a : σ) :
    Algebra.PreSubmersivePresentation R (CoordinateRing F) σ Unit where
  __ := presentation F
  map := fun _ => a
  map_inj := fun _ _ _ => Subsingleton.elim _ _

/-- The actual presentation Jacobian is the quotient image of the chart partial derivative. -/
theorem preSubmersivePresentation_jacobian
    (F : MvPolynomial (σ ⊕ Unit) R) (a : σ) :
    (preSubmersivePresentation F a).jacobian =
      Ideal.Quotient.mk _ (pderiv a (dehomogenize F)) := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rw [Algebra.Generators.algebraMap_apply]
  change aeval (presentation F).val (pderiv a (dehomogenize F)) = _
  have hv : (presentation F).val = fun i => Ideal.Quotient.mk _ (X i) := by
    funext i
    exact presentation_val F i
  rw [hv]
  have he : (aeval (fun i => Ideal.Quotient.mk (Ideal.span {dehomogenize F}) (X i)) :
      MvPolynomial σ R →ₐ[R] CoordinateRing F) = Ideal.Quotient.mkₐ R _ := by
    ext i
    simp
  rw [he]
  rfl
end NcCubic.Geometry.AffineChart
