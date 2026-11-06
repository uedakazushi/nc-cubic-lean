/- Polynomial part of the standard-chart comparison for a projective hypersurface.
The distinguished homogeneous coordinate is indexed by Sum.inr (). -/
module
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.AffineChart
open MvPolynomial
open scoped BigOperators
variable {R σ : Type*} [CommRing R]

/-- Substitute one for the distinguished homogeneous coordinate. -/
def dehomogenize (F : MvPolynomial (σ ⊕ Unit) R) : MvPolynomial σ R :=
  aeval (Sum.elim X (fun _ : Unit => 1)) F

/-- A point of the standard chart, in homogeneous coordinates with pivot one. -/
def lift (x : σ → R) : σ ⊕ Unit → R := Sum.elim x (fun _ => 1)

/-- Dehomogenization commutes with differentiation in the affine directions. -/
theorem pderiv_dehomogenize (F : MvPolynomial (σ ⊕ Unit) R) (i : σ) :
    pderiv i (dehomogenize F) = dehomogenize (pderiv (Sum.inl i) F) := by
  simpa only [dehomogenize, Function.comp_def, map_one] using
    (aeval_sumElim_pderiv_inl F (fun _ : Unit => (1 : R)) i).symm

/-- Evaluation on the affine chart is evaluation at its normalized homogeneous point. -/
theorem eval_dehomogenize (F : MvPolynomial (σ ⊕ Unit) R) (x : σ → R) :
    eval x (dehomogenize F) = eval (lift x) F := by
  classical
  induction F using MvPolynomial.induction_on with
  | C r => simp [dehomogenize]
  | add p q hp hq => simp_all [dehomogenize]
  | mul_X p i hp =>
      cases i <;> simp_all [dehomogenize, lift]

/-- The Jacobian entries of the affine equation are the non-pivot entries of the
homogeneous Jacobian at the corresponding normalized point. -/
theorem eval_pderiv_dehomogenize (F : MvPolynomial (σ ⊕ Unit) R) (x : σ → R) (i : σ) :
    eval x (pderiv i (dehomogenize F)) = eval (lift x) (pderiv (Sum.inl i) F) := by
  rw [pderiv_dehomogenize, eval_dehomogenize]

/-- On the hypersurface, Euler determines the pivot derivative from the affine
ones. Consequently the two coordinate Jacobian tests agree on this chart. -/
theorem gradient_zero_iff_on_hypersurface [Fintype σ]
    (F : MvPolynomial (σ ⊕ Unit) R) {d : ℕ} (hF : F.IsHomogeneous d)
    (x : σ → R) (hzero : eval x (dehomogenize F) = 0) :
    (∀ i : σ, eval x (pderiv i (dehomogenize F)) = 0) ↔
      ∀ i : σ ⊕ Unit, eval (lift x) (pderiv i F) = 0 := by
  classical
  constructor
  · intro h
    have hhom : eval (lift x) F = 0 := by rwa [← eval_dehomogenize]
    have he := congrArg (eval (lift x)) hF.sum_X_mul_pderiv
    simp only [map_sum, map_mul, eval_X, map_nsmul, hhom, nsmul_zero] at he
    rw [Fintype.sum_sum_type] at he
    have hn : ∀ i : σ, eval (lift x) (pderiv (Sum.inl i) F) = 0 := by
      intro i
      rw [← eval_pderiv_dehomogenize]
      exact h i
    have hp : eval (lift x) (pderiv (Sum.inr ()) F) = 0 := by
      simp only [hn, mul_zero, Finset.sum_const_zero, zero_add] at he
      simpa [lift] using he
    intro i
    cases i with
    | inl i => exact hn i
    | inr u => cases u; exact hp
  · intro h i
    rw [eval_pderiv_dehomogenize]
    exact h (Sum.inl i)
/-- A normalized homogeneous point is never the zero vector. -/
theorem lift_ne_zero [Nontrivial R] (x : σ → R) : lift x ≠ 0 := by
  intro h
  have hi := congrFun h (Sum.inr ())
  simp [lift] at hi

/-- The nonvanishing derivative test on the affine hypersurface agrees with the
homogeneous gradient test, before the scheme-smoothness comparison is applied. -/
theorem exists_nonzero_derivative_iff [Fintype σ]
    (F : MvPolynomial (σ ⊕ Unit) R) {d : ℕ} (hF : F.IsHomogeneous d)
    (x : σ → R) (hzero : eval x (dehomogenize F) = 0) :
    (∃ i : σ, eval x (pderiv i (dehomogenize F)) ≠ 0) ↔
      ∃ i : σ ⊕ Unit, eval (lift x) (pderiv i F) ≠ 0 := by
  classical
  simpa only [not_forall] using not_congr (gradient_zero_iff_on_hypersurface F hF x hzero)
/-- The coordinate ring of the affine hypersurface in this standard chart. -/
abbrev CoordinateRing (F : MvPolynomial (σ ⊕ Unit) R) :=
  MvPolynomial σ R ⧸ Ideal.span ({dehomogenize F} : Set (MvPolynomial σ R))

/-- An actual chart solution defines a ring homomorphism from its coordinate ring. -/
def pointEvaluation (F : MvPolynomial (σ ⊕ Unit) R) (x : σ → R)
    (hx : eval x (dehomogenize F) = 0) : CoordinateRing F →+* R :=
  Ideal.Quotient.lift _ (eval x) (by
    change Ideal.span ({dehomogenize F} : Set (MvPolynomial σ R)) ≤ RingHom.ker (eval x)
    apply Ideal.span_le.mpr
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact hx)

/-- The quotient-point map evaluates the polynomial representing a function. -/
theorem pointEvaluation_mk (F : MvPolynomial (σ ⊕ Unit) R) (x : σ → R)
    (hx : eval x (dehomogenize F) = 0) (p : MvPolynomial σ R) :
    pointEvaluation F x hx (Ideal.Quotient.mk _ p) = eval x p := by
  simp [pointEvaluation]
end NcCubic.Geometry.AffineChart
