/- General polynomial biderivations and their coordinate Jacobi criterion. -/
module

public import NcCubic.Coordinates
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section
namespace NcCubic.JacobiCriterion
open MvPolynomial

/-- A skew biderivation whose coefficient scalars are central. -/
structure PolynomialBracket (R σ : Type*) [CommRing R] where
  bracket : MvPolynomial σ R → MvPolynomial σ R → MvPolynomial σ R
  add_left : ∀ a b c, bracket (a + b) c = bracket a c + bracket b c
  add_right : ∀ a b c, bracket a (b + c) = bracket a b + bracket a c
  mul_left : ∀ a b c, bracket (a * b) c = a * bracket b c + b * bracket a c
  mul_right : ∀ a b c, bracket a (b * c) = bracket a b * c + b * bracket a c
  const_left : ∀ r a, bracket (C r) a = 0
  const_right : ∀ a r, bracket a (C r) = 0
  skew : ∀ a b, bracket a b = -bracket b a

variable {R σ : Type*} [CommRing R]

def jacobiator (B : PolynomialBracket R σ) (a b c : MvPolynomial σ R) :=
  B.bracket a (B.bracket b c) + B.bracket b (B.bracket c a) +
    B.bracket c (B.bracket a b)

namespace PolynomialBracket
variable (B : PolynomialBracket R σ)

theorem jacobiator_cyclic (a b c : MvPolynomial σ R) :
    jacobiator B a b c = jacobiator B b c a := by
  unfold jacobiator
  ring

theorem jacobiator_add_left (a b c d : MvPolynomial σ R) :
    jacobiator B (a + b) c d = jacobiator B a c d + jacobiator B b c d := by
  simp only [jacobiator, B.add_left, B.add_right]
  ring

theorem jacobiator_mul_left (a b c d : MvPolynomial σ R) :
    jacobiator B (a * b) c d = a * jacobiator B b c d + b * jacobiator B a c d := by
  simp only [jacobiator, B.mul_left, B.mul_right, B.add_right]
  rw [B.skew c a, B.skew b c]
  ring

theorem jacobiator_const_left (r : R) (a b : MvPolynomial σ R) :
    jacobiator B (C r) a b = 0 := by
  simp only [jacobiator, B.const_left, B.const_right]
  have hz (c : MvPolynomial σ R) : B.bracket c 0 = 0 := by
    simpa only [map_zero] using B.const_right c 0
  simp [hz]

/-- Checking a triderivation on the polynomial generators suffices. -/
theorem jacobi_of_coordinates
    (h : ∀ i j k : σ, jacobiator B (X i) (X j) (X k) = 0) :
    ∀ a b c : MvPolynomial σ R, jacobiator B a b c = 0 := by
  have extend (b c : MvPolynomial σ R)
      (hX : ∀ i, jacobiator B (X i) b c = 0) :
      ∀ a, jacobiator B a b c = 0 := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C r => exact B.jacobiator_const_left r b c
    | add p q hp hq => rw [B.jacobiator_add_left, hp, hq, add_zero]
    | mul_X p i hp => rw [B.jacobiator_mul_left, hp, hX, mul_zero, mul_zero, add_zero]
  intro a b c
  apply extend b c
  intro i
  rw [B.jacobiator_cyclic]
  apply extend c (X i)
  intro j
  rw [B.jacobiator_cyclic]
  apply extend (X i) (X j)
  intro k
  rw [B.jacobiator_cyclic]
  exact h i j k

end PolynomialBracket
open scoped BigOperators

/-- The coefficient formula is a scalar-central biderivation when q is skew. -/
def coefficientBracket {N : ℕ} (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, q j i = -q i j) : PolynomialBracket ℂ (Fin N) where
  bracket := bracketFromCoefficients q
  add_left a b c := by
    rw [bracket_skew q hq c (a + b), bracket_add_right,
      bracket_skew q hq a c, bracket_skew q hq b c]
    ring
  add_right := bracket_add_right q
  mul_left a b c := by
    rw [bracket_skew q hq c (a * b), bracket_leibniz_right,
      bracket_skew q hq a c, bracket_skew q hq b c]
    ring
  mul_right := bracket_leibniz_right q
  const_left r a := by
    rw [bracket_skew q hq a (C r), bracket_constant_right, neg_zero]
  const_right := bracket_constant_right q
  skew a b := bracket_skew q hq b a

/-- Coordinate polynomials evaluate the coefficient biderivation directly. -/
theorem bracket_coordinate_left {N : ℕ} (q : Fin N → Fin N → CubicPolynomial N)
    (i : Fin N) (f : CubicPolynomial N) :
    bracketFromCoefficients q (X i) f = ∑ j, q i j * pderiv j f := by
  simp [bracketFromCoefficients, pderiv_X, Pi.single_apply, mul_ite, ite_mul]

theorem bracket_coordinates {N : ℕ} (q : Fin N → Fin N → CubicPolynomial N)
    (i j : Fin N) : bracketFromCoefficients q (X i) (X j) = q i j := by
  simp [bracket_coordinate_left, pderiv_X, Pi.single_apply, mul_ite]

/-- No smoothness or homogeneity is needed to reduce polynomial Jacobi to generators. -/
theorem satisfiesJacobi_iff_coordinates {N : ℕ}
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j, q j i = -q i j) :
    SatisfiesJacobi (bracketFromCoefficients q) ↔
      ∀ i j k, ∑ r, (q i r * pderiv r (q j k) +
        q j r * pderiv r (q k i) + q k r * pderiv r (q i j)) = 0 := by
  constructor
  · intro h i j k
    have hi := h (X i) (X j) (X k)
    rw [bracket_coordinates, bracket_coordinates, bracket_coordinates] at hi
    simpa only [bracket_coordinate_left, Finset.sum_add_distrib] using hi
  · intro h
    apply (coefficientBracket q hq).jacobi_of_coordinates
    intro i j k
    change bracketFromCoefficients q (X i) (bracketFromCoefficients q (X j) (X k)) +
      bracketFromCoefficients q (X j) (bracketFromCoefficients q (X k) (X i)) +
      bracketFromCoefficients q (X k) (bracketFromCoefficients q (X i) (X j)) = 0
    rw [bracket_coordinates, bracket_coordinates, bracket_coordinates]
    simpa only [bracket_coordinate_left, Finset.sum_add_distrib] using h i j k

/-- One cyclic term of the coordinate Jacobiator, grouped by the gradient. -/
theorem contraction_cyclic_expansion {N : ℕ} (F : CubicPolynomial N) (P : Trivector N)
    (i j k : Fin N) :
    (∑ r, contractionCoefficients F P i r *
      pderiv r (contractionCoefficients F P j k)) =
    ∑ a, pderiv a F * ∑ r, ∑ b,
      C (trivectorCoefficient P i r a * trivectorCoefficient P j k b) *
        pderiv r (pderiv b F) := by
  simp only [contractionCoefficients, map_sum, pderiv_mul, pderiv_C,
    zero_mul, zero_add, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, r]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  rw [map_mul]
  ring

/-- The linear Hessian coefficient in the coordinate Jacobiator. -/
def jacobiLinearCoefficient {N : ℕ} (F : CubicPolynomial N) (P : Trivector N)
    (i j k a : Fin N) : CubicPolynomial N :=
  ∑ r, ∑ b,
    C (trivectorCoefficient P i r a * trivectorCoefficient P j k b +
      trivectorCoefficient P j r a * trivectorCoefficient P k i b +
      trivectorCoefficient P k r a * trivectorCoefficient P i j b) *
        pderiv r (pderiv b F)

/-- Exact coordinate Jacobi expansion, without ignoring any scalar or sign. -/
theorem contraction_jacobi_expansion {N : ℕ} (F : CubicPolynomial N) (P : Trivector N)
    (i j k : Fin N) :
    (∑ r, (contractionCoefficients F P i r * pderiv r (contractionCoefficients F P j k) +
      contractionCoefficients F P j r * pderiv r (contractionCoefficients F P k i) +
      contractionCoefficients F P k r * pderiv r (contractionCoefficients F P i j))) =
    ∑ a, pderiv a F * jacobiLinearCoefficient F P i j k a := by
  simp only [Finset.sum_add_distrib]
  rw [contraction_cyclic_expansion, contraction_cyclic_expansion,
    contraction_cyclic_expansion]
  simp only [jacobiLinearCoefficient, map_add, add_mul, Finset.sum_add_distrib, mul_add]

/-- The remaining transposition needed for the Hessian compatibility signs. -/
theorem coefficient_swap_middle {N : ℕ} (P : Trivector N) (i r a : Fin N) :
    trivectorCoefficient P i r a = -trivectorCoefficient P i a r := by
  calc
    trivectorCoefficient P i r a = -trivectorCoefficient P a r i :=
      trivectorCoefficient_swap_last P a r i
    _ = trivectorCoefficient P r a i := by
      rw [trivectorCoefficient_swap_first P r a i, neg_neg]
    _ = -trivectorCoefficient P i a r := trivectorCoefficient_swap_last P i a r

/-- K(P) evaluated on four coordinate covectors and a polynomial Hessian. -/
def compatibilityCoefficient {N : ℕ} (P : Trivector N)
    (H : Fin N → Fin N → CubicPolynomial N) (i j k a : Fin N) : CubicPolynomial N :=
  ∑ r, ∑ b,
    C (trivectorCoefficient P i j r * trivectorCoefficient P k a b +
      trivectorCoefficient P j k r * trivectorCoefficient P i a b +
      trivectorCoefficient P k i r * trivectorCoefficient P j a b) * H r b

/-- Under the project's convention, the Jacobi coefficient is minus K, not K. -/
theorem jacobiLinearCoefficient_eq_neg_compatibility {N : ℕ}
    (F : CubicPolynomial N) (P : Trivector N) (i j k a : Fin N) :
    jacobiLinearCoefficient F P i j k a =
      -compatibilityCoefficient P (fun r b => pderiv r (pderiv b F)) i j k a := by
  unfold jacobiLinearCoefficient compatibilityCoefficient
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  rw [coefficient_swap_middle P i b a, coefficient_swap_middle P j b a,
    coefficient_swap_middle P k b a]
  simp only [map_add, map_mul, map_neg]
  rw [pderiv_comm b r]
  ring

/-- For a cubic potential the coefficients multiplying its gradient are linear. -/
theorem jacobiLinearCoefficient_homogeneous {N : ℕ}
    {F : CubicPolynomial N} (hF : F.IsHomogeneous 3) (P : Trivector N)
    (i j k a : Fin N) : (jacobiLinearCoefficient F P i j k a).IsHomogeneous 1 := by
  unfold jacobiLinearCoefficient
  apply IsHomogeneous.sum
  intro r hr
  apply IsHomogeneous.sum
  intro b hb
  exact hF.pderiv.pderiv.C_mul _

/-- Hessian compatibility implies the full polynomial Jacobi identity unconditionally. -/
theorem jacobi_of_compatibility {N : ℕ} (F : CubicPolynomial N) (P : Trivector N)
    (h : ∀ i j k a,
      compatibilityCoefficient P (fun r b => pderiv r (pderiv b F)) i j k a = 0) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) := by
  apply (satisfiesJacobi_iff_coordinates _ (contraction_skew F P)).2
  intro i j k
  rw [contraction_jacobi_expansion]
  apply Finset.sum_eq_zero
  intro a ha
  rw [jacobiLinearCoefficient_eq_neg_compatibility, h, neg_zero, mul_zero]

/-- The reverse direction isolates precisely the low-degree syzygy obligation.
This is not a proof that the gradient of a smooth cubic has that property. -/
theorem jacobi_iff_compatibility_of_no_linear_syzygy {N : ℕ}
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3)
    (hsyzygy : ∀ A : Fin N → CubicPolynomial N,
      (∀ a, (A a).IsHomogeneous 1) → (∑ a, pderiv a F * A a) = 0 → ∀ a, A a = 0) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) ↔
      ∀ i j k a,
        compatibilityCoefficient P (fun r b => pderiv r (pderiv b F)) i j k a = 0 := by
  constructor
  · intro h i j k a
    have hcoord := (satisfiesJacobi_iff_coordinates _ (contraction_skew F P)).1 h i j k
    rw [contraction_jacobi_expansion] at hcoord
    have hz := hsyzygy (jacobiLinearCoefficient F P i j k)
      (fun b => jacobiLinearCoefficient_homogeneous hF P i j k b) hcoord a
    rw [jacobiLinearCoefficient_eq_neg_compatibility, neg_eq_zero] at hz
    exact hz
  · exact jacobi_of_compatibility F P

end NcCubic.JacobiCriterion
