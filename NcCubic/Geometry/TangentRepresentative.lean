/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.

The coefficient correction in Proposition 2.3. Geometric tangency is an explicit
input; no assertion of projective section representability is made here.
-/
module
public import NcCubic.Geometry.RepresentativeUniqueness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

def gradientContract2 (F : CubicPolynomial N)
    (q : Fin N → Fin N → CubicPolynomial N) (j : Fin N) :=
  ∑ i, q i j * pderiv i F

def vectorDerivative (F : CubicPolynomial N) (A : Fin N → CubicPolynomial N) :=
  ∑ i, A i * pderiv i F

theorem gradientContract2_eulerWedge (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (A : Fin N → CubicPolynomial N) (j : Fin N) :
    gradientContract2 F (eulerWedge1 A) j =
      3 * F * A j - vectorDerivative F A * X j := by
  have he := CubicDifferential.euler hF
  simp only [nsmul_eq_mul] at he
  unfold gradientContract2 eulerWedge1 vectorDerivative
  simp only [sub_mul, Finset.sum_sub_distrib]
  calc
    _ = (∑ i, X i * pderiv i F) * A j - (∑ i, A i * pderiv i F) * X j := by
      simp only [Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
    _ = _ := by rw [he]; norm_num

theorem gradientContract2_twice_zero (F : CubicPolynomial N)
    (q : Fin N → Fin N → CubicPolynomial N) (hskew : ∀ i j, q j i = -q i j) :
    ∑ j, gradientContract2 F q j * pderiv j F = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  unfold gradientContract2
  simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hskew]
  ring

theorem tangent_scalar_relation (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hne : F ≠ 0) (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j) (A : Fin N → CubicPolynomial N)
    (h : CubicPolynomial N)
    (htangent : ∀ j, gradientContract2 F B j = F * A j + h * X j) :
    vectorDerivative F A + 3 * h = 0 := by
  have hz := gradientContract2_twice_zero F B hskew
  simp_rw [htangent] at hz
  have he := CubicDifferential.euler hF
  simp only [nsmul_eq_mul] at he
  have hx : F * (vectorDerivative F A + 3 * h) = 0 := by
    calc
      _ = F * (∑ j, A j * pderiv j F) + h * (∑ j, X j * pderiv j F) := by
        rw [he]
        unfold vectorDerivative
        ring
      _ = ∑ j, (F * A j + h * X j) * pderiv j F := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := hz
  exact (mul_eq_zero.mp hx).resolve_left hne

theorem corrected_tangent_representative (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hne : F ≠ 0) (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j) (A : Fin N → CubicPolynomial N)
    (h : CubicPolynomial N)
    (htangent : ∀ j, gradientContract2 F B j = F * A j + h * X j) (j : Fin N) :
    gradientContract2 F (fun i j => B i j - (1 / 3 : ℂ) • eulerWedge1 A i j) j = 0 := by
  have hs := tangent_scalar_relation F hF hne B hskew A h htangent
  have hw := gradientContract2_eulerWedge F hF A j
  unfold gradientContract2 at *
  simp only [sub_mul, Finset.sum_sub_distrib, smul_eq_C_mul,
    mul_assoc, ← Finset.mul_sum]
  rw [htangent j, hw]
  have hc : (C (1 / 3 : ℂ) : CubicPolynomial N) * 3 = 1 := by
    calc
      _ = C ((1 / 3 : ℂ) * 3) := by simp only [map_mul, map_ofNat]
      _ = 1 := by norm_num
  have hs' : vectorDerivative F A = -(3 * h) := eq_neg_iff_add_eq_zero.mpr hs
  rw [hs']
  calc
    _ = (1 - C (1 / 3 : ℂ) * 3) * (F * A j + h * X j) := by ring
    _ = 0 := by rw [hc]; ring

/-- The Euler correction preserves skew-symmetry. -/
theorem corrected_tangent_skew (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j) (A : Fin N → CubicPolynomial N) (i j : Fin N) :
    B j i - (1 / 3 : ℂ) • eulerWedge1 A j i =
      -(B i j - (1 / 3 : ℂ) • eulerWedge1 A i j) := by
  rw [hskew]
  simp only [eulerWedge1, smul_eq_C_mul]
  ring

/-- A linear Euler correction of a quadratic bivector stays quadratic. -/
theorem corrected_tangent_homogeneous (B : Fin N → Fin N → CubicPolynomial N)
    (hB : ∀ i j, (B i j).IsHomogeneous 2) (A : Fin N → CubicPolynomial N)
    (hA : ∀ i, (A i).IsHomogeneous 1) (i j : Fin N) :
    (B i j - (1 / 3 : ℂ) • eulerWedge1 A i j).IsHomogeneous 2 := by
  rw [smul_eq_C_mul]
  apply (hB i j).sub
  apply IsHomogeneous.C_mul
  exact ((isHomogeneous_X ℂ i).mul (hA j)).sub ((isHomogeneous_X ℂ j).mul (hA i))

/-- The tangency equation produces a genuine horizontal quadratic representative.
The displayed tangency is still the geometric input that must be established
from the actual hypersurface tangent sheaf. -/
theorem exists_horizontal_representative (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hne : F ≠ 0) (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j) (hB : ∀ i j, (B i j).IsHomogeneous 2)
    (A : Fin N → CubicPolynomial N) (hA : ∀ i, (A i).IsHomogeneous 1)
    (h : CubicPolynomial N)
    (htangent : ∀ j, gradientContract2 F B j = F * A j + h * X j) :
    ∃ q : Fin N → Fin N → CubicPolynomial N,
      (∀ i j, q j i = -q i j) ∧ (∀ i j, (q i j).IsHomogeneous 2) ∧
      (∀ j, gradientContract2 F q j = 0) ∧
      (∀ i j, q i j = B i j - (1 / 3 : ℂ) • eulerWedge1 A i j) := by
  refine ⟨fun i j => B i j - (1 / 3 : ℂ) • eulerWedge1 A i j, ?_, ?_, ?_, ?_⟩
  · exact corrected_tangent_skew B hskew A
  · exact corrected_tangent_homogeneous B hB A hA
  · exact corrected_tangent_representative F hF hne B hskew A h htangent
  · intro i j; rfl
end NcCubic.Geometry
