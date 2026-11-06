/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.KahlerBracket
public import NcCubic.Geometry.BivectorCoordinates
public import NcCubic.JacobiCriterion
public import Mathlib.RingTheory.Kaehler.Polynomial
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}
/-- Polynomial vector coefficients identify with the actual dual of the
polynomial Kähler module through the coordinate differential basis. -/
def polynomialTangentEquiv :
    (Fin N → CubicPolynomial N) ≃ₗ[CubicPolynomial N]
      Module.Dual (CubicPolynomial N) (KaehlerDifferential ℂ (CubicPolynomial N)) :=
  (KaehlerDifferential.mvPolynomialBasis ℂ (Fin N)).dualBasis.equivFun.symm

@[simp] theorem polynomialTangentEquiv_basis_d (i : Fin N) (f : CubicPolynomial N) :
    polynomialTangentEquiv (KoszulCoordinates.basisVector i)
      (KaehlerDifferential.D ℂ (CubicPolynomial N) f) = pderiv i f := by
  simp [polynomialTangentEquiv, Module.Basis.equivFun_symm_apply,
    KoszulCoordinates.basisVector, Pi.single_apply,
    KaehlerDifferential.mvPolynomialBasis_repr_apply]

/-- The standard vector-field formula is evaluation on the actual differential. -/
theorem polynomialTangentEquiv_d (v : Fin N → CubicPolynomial N) (f : CubicPolynomial N) :
    polynomialTangentEquiv v (KaehlerDifferential.D ℂ (CubicPolynomial N) f) =
      ∑ i, v i * pderiv i f := by
  have hv : v = ∑ i, v i • KoszulCoordinates.basisVector i := by
    ext j
    simp [KoszulCoordinates.basisVector, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    polynomialTangentEquiv_basis_d, smul_eq_mul]

/-- The actual tangent bivector with the specified polynomial coefficients. -/
def polynomialBivector (q : Fin N → Fin N → CubicPolynomial N) :
    ⋀[CubicPolynomial N]^2
      (Module.Dual (CubicPolynomial N) (KaehlerDifferential ℂ (CubicPolynomial N))) :=
  exteriorPower.map 2 polynomialTangentEquiv.toLinearMap (BivectorCoordinates.bivector q)

/-- Evaluation of the genuine tangent bivector is the original coordinate bracket. -/
theorem polynomialBivector_d_wedge_d (q : Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ i j, q j i = -q i j) (f g : CubicPolynomial N) :
    exteriorPower.pairingDual (CubicPolynomial N) (KaehlerDifferential ℂ (CubicPolynomial N)) 2
      (polynomialBivector q)
      (exteriorPower.ιMulti (CubicPolynomial N) 2
        ![KaehlerDifferential.D ℂ (CubicPolynomial N) f,
          KaehlerDifferential.D ℂ (CubicPolynomial N) g]) =
      bracketFromCoefficients q f g := by
  simp only [polynomialBivector, BivectorCoordinates.bivector, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp only [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
    Matrix.det_fin_two, Matrix.of_apply, Function.comp_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, LinearEquiv.coe_coe,
    polynomialTangentEquiv_basis_d]
  have hc : (C (1 / 2 : ℂ) : CubicPolynomial N) + C (1 / 2 : ℂ) = 1 := by
    rw [← map_add]
    norm_num
  simp only [mul_sub, Finset.sum_sub_distrib, bracketFromCoefficients]
  have hh : (∑ i, ∑ j, C (1/2 : ℂ) * q i j * (pderiv i g * pderiv j f)) =
      -(∑ i, ∑ j, C (1/2 : ℂ) * q i j * (pderiv i f * pderiv j g)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
    ring
  have hh' : (∑ i, ∑ j, C (1/2 : ℂ) * q i j * (pderiv j f * pderiv i g)) =
      -(∑ i, ∑ j, C (1/2 : ℂ) * q i j * (pderiv i f * pderiv j g)) := by
    simpa only [mul_comm] using hh
  rw [hh']
  rw [sub_neg_eq_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination (q i j * pderiv i f * pderiv j g) * hc

/-- Coordinate differentials recover the original skew coefficient array. -/
@[simp] theorem polynomialBivector_coordinates (q : Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ i j, q j i = -q i j) (i j : Fin N) :
    exteriorPower.pairingDual (CubicPolynomial N) (KaehlerDifferential ℂ (CubicPolynomial N)) 2
      (polynomialBivector q)
      (exteriorPower.ιMulti (CubicPolynomial N) 2
        ![KaehlerDifferential.D ℂ (CubicPolynomial N) (X i),
          KaehlerDifferential.D ℂ (CubicPolynomial N) (X j)]) = q i j := by
  rw [polynomialBivector_d_wedge_d q hs, JacobiCriterion.bracket_coordinates]

/-- Actual tangent bivectors do not identify two different skew arrays. -/
theorem polynomialBivector_eq_iff (q r : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, q j i = -q i j) (hr : ∀ i j, r j i = -r i j) :
    polynomialBivector q = polynomialBivector r ↔ q = r := by
  constructor
  · intro h
    funext i j
    have hh := congrArg (fun z =>
      exteriorPower.pairingDual (CubicPolynomial N)
        (KaehlerDifferential ℂ (CubicPolynomial N)) 2 z
        (exteriorPower.ιMulti (CubicPolynomial N) 2
          ![KaehlerDifferential.D ℂ (CubicPolynomial N) (X i),
            KaehlerDifferential.D ℂ (CubicPolynomial N) (X j)])) h
    simpa only [polynomialBivector_coordinates q hq, polynomialBivector_coordinates r hr] using hh
  · rintro rfl
    rfl
end NcCubic.Geometry
