/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Statement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

theorem bracket_add_right (q : Fin N → Fin N → CubicPolynomial N) (f g h : CubicPolynomial N) :
    bracketFromCoefficients q f (g + h) =
      bracketFromCoefficients q f g + bracketFromCoefficients q f h := by
  simp [bracketFromCoefficients, map_add, mul_add, Finset.sum_add_distrib]

theorem bracket_leibniz_right (q : Fin N → Fin N → CubicPolynomial N) (f g h : CubicPolynomial N) :
    bracketFromCoefficients q f (g * h) =
      bracketFromCoefficients q f g * h + g * bracketFromCoefficients q f h := by
  simp only [bracketFromCoefficients, pderiv_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

theorem bracket_constant_right (q : Fin N → Fin N → CubicPolynomial N)
    (f : CubicPolynomial N) (c : ℂ) : bracketFromCoefficients q f (C c) = 0 := by
  simp [bracketFromCoefficients]

theorem trivectorCoefficient_swap_first (P : Trivector N) (i j a : Fin N) :
    trivectorCoefficient P j i a = -trivectorCoefficient P i j a := by
  have h := P.map_swap ![coordinateCovector i, coordinateCovector j, coordinateCovector a]
    (show (0 : Fin 3) ≠ 1 by decide)
  have hv : (![coordinateCovector i, coordinateCovector j, coordinateCovector a] ∘
      Equiv.swap (0 : Fin 3) 1) = ![coordinateCovector j, coordinateCovector i, coordinateCovector a] := by
    funext k; fin_cases k <;> norm_num [Equiv.swap_apply_def]
  simpa [hv, trivectorCoefficient] using h

theorem contraction_skew (F : CubicPolynomial N) (P : Trivector N) (i j : Fin N) :
    contractionCoefficients F P j i = -contractionCoefficients F P i j := by
  unfold contractionCoefficients
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [trivectorCoefficient_swap_first, map_neg, neg_mul]

theorem bracket_skew (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, q j i = -q i j) (f g : CubicPolynomial N) :
    bracketFromCoefficients q g f = -bracketFromCoefficients q f g := by
  rw [bracketFromCoefficients, Finset.sum_comm]
  simp only [bracketFromCoefficients, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hq]
  ring
theorem trivectorCoefficient_swap_last (P : Trivector N) (i j a : Fin N) :
    trivectorCoefficient P a j i = -trivectorCoefficient P i j a := by
  have h := P.map_swap ![coordinateCovector i, coordinateCovector j, coordinateCovector a]
    (show (0 : Fin 3) ≠ 2 by decide)
  have hv : (![coordinateCovector i, coordinateCovector j, coordinateCovector a] ∘
      Equiv.swap (0 : Fin 3) 2) = ![coordinateCovector a, coordinateCovector j, coordinateCovector i] := by
    funext k; fin_cases k <;> norm_num [Equiv.swap_apply_def]
  simpa [hv, trivectorCoefficient] using h

theorem contraction_gradient_zero (F : CubicPolynomial N) (P : Trivector N) (j : Fin N) :
    ∑ i, contractionCoefficients F P i j * pderiv i F = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  simp only [contractionCoefficients, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs => rw [trivectorCoefficient_swap_last, map_neg]
  ring

theorem contraction_potential_casimir (F g : CubicPolynomial N) (P : Trivector N) :
    bracketFromCoefficients (contractionCoefficients F P) F g = 0 := by
  unfold bracketFromCoefficients
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, contraction_gradient_zero, zero_mul, Finset.sum_const_zero]


/-- Expansion of a covector in the standard coordinate covectors. -/
theorem covector_eq_sum {N : ℕ} (α : Covector N) :
    α = ∑ i : Fin N, α (Pi.single i 1) • coordinateCovector i := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, coordinateCovector, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul]
  have hx : x = ∑ i : Fin N, x i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end NcCubic
