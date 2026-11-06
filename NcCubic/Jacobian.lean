/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# One Jacobian block

This is the local algebra in the converse direction of Theorem 1.1(3) of
`cubic_poisson_paper_20261104.pdf`, printed page 7. The construction works over
any commutative coefficient ring and for an arbitrary polynomial potential.
The variable type may include extra, central variables.

The theorems below concern one block. They do not assert the forward
classification or the compatibility of a family of different blocks.
-/

@[expose] public section

noncomputable section

namespace NcCubic.Jacobian

open MvPolynomial

variable {R : Type*} {σ : Type*} [CommRing R]

/-- The Jacobian bracket in the three chosen derivative directions.
Its sign convention gives `{X i, X j} = ∂ₖF` for distinct `i`, `j`, `k`. -/
def bracket (i j k : σ) (F a b : MvPolynomial σ R) : MvPolynomial σ R :=
  pderiv i F * (pderiv j a * pderiv k b - pderiv k a * pderiv j b) +
  pderiv j F * (pderiv k a * pderiv i b - pderiv i a * pderiv k b) +
  pderiv k F * (pderiv i a * pderiv j b - pderiv j a * pderiv i b)

theorem skew (i j k : σ) (F a b : MvPolynomial σ R) :
    bracket i j k F a b = -bracket i j k F b a := by
  unfold bracket
  ring

@[simp]
theorem self (i j k : σ) (F a : MvPolynomial σ R) :
    bracket i j k F a a = 0 := by
  unfold bracket
  ring

theorem add_right (i j k : σ) (F a b c : MvPolynomial σ R) :
    bracket i j k F a (b + c) =
      bracket i j k F a b + bracket i j k F a c := by
  simp only [bracket, map_add]
  ring

theorem leibniz_right (i j k : σ) (F a b c : MvPolynomial σ R) :
    bracket i j k F a (b * c) =
      bracket i j k F a b * c + b * bracket i j k F a c := by
  simp only [bracket, pderiv_mul]
  ring

/-- The potential is a Casimir for its Jacobian bracket. -/
@[simp]
theorem potential_casimir (i j k : σ) (F a : MvPolynomial σ R) :
    bracket i j k F F a = 0 := by
  unfold bracket
  ring

/-- Coefficient scalars are central. -/
@[simp]
theorem constant_central (i j k : σ) (F a : MvPolynomial σ R) (r : R) :
    bracket i j k F (C r) a = 0 := by
  simp [bracket]

/-- Variables outside the three derivative directions are central. -/
theorem other_variable_central (i j k u : σ) (F a : MvPolynomial σ R)
    (hi : u ≠ i) (hj : u ≠ j) (hk : u ≠ k) :
    bracket i j k F (X u) a = 0 := by
  simp [bracket, pderiv_X_of_ne hi, pderiv_X_of_ne hj, pderiv_X_of_ne hk]

/-- The coordinate convention of equation (1.2) in the source paper. -/
theorem coordinate_bracket (i j k : σ) (F : MvPolynomial σ R)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    bracket i j k F (X i) (X j) = pderiv k F := by
  simp only [bracket, pderiv_X_self, pderiv_X_of_ne hij,
    pderiv_X_of_ne (Ne.symm hij), pderiv_X_of_ne hik, pderiv_X_of_ne hjk]
  ring

/-- The full Jacobi identity on arbitrary polynomials, not only on coordinate
generators. The proof uses the commutation of mixed polynomial derivatives. -/
theorem jacobi (i j k : σ) (F a b c : MvPolynomial σ R) :
    bracket i j k F a (bracket i j k F b c) +
      bracket i j k F b (bracket i j k F c a) +
      bracket i j k F c (bracket i j k F a b) = 0 := by
  simp only [bracket, map_add, map_sub, pderiv_mul]
  simp only [pderiv_comm]
  ring

end NcCubic.Jacobian
