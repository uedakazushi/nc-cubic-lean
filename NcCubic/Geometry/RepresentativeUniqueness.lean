/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Divergence
public import NcCubic.CubicDifferential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators

/-- A polynomial whose gradient has only the origin as a zero is nonzero
when there is at least one variable. -/
theorem polynomial_ne_zero_of_isolated_gradient {N : ℕ} (hN : 0 < N)
    {F : CubicPolynomial N} (hgrad : HasIsolatedGradientZero F) : F ≠ 0 := by
  intro hF
  let i : Fin N := ⟨0,hN⟩
  have hz := hgrad (Pi.single i 1) (by simp [hF])
  have hi := congrFun hz i
  simp at hi

/-- A radial proportionality relation forces the Euler wedge to vanish.
This is cancellation in the polynomial domain, so irreducibility of F and
degree assumptions on Z are unnecessary. -/
theorem eulerWedge1_eq_zero_of_radial_relation {N : ℕ}
    (F H : CubicPolynomial N) (hF : F ≠ 0) (Z : Fin N → CubicPolynomial N)
    (hrel : ∀ i, 3 * F * Z i = H * X i) (i j : Fin N) :
    eulerWedge1 Z i j = 0 := by
  have hz : 3 * F * eulerWedge1 Z i j = 0 := by
    unfold eulerWedge1
    linear_combination (X i) * hrel j - (X j) * hrel i
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hF)

/-- Euler's identity turns the Casimir condition on an Euler wedge into
radial proportionality, with the directional derivative of F as scalar. -/
theorem radial_relation_of_eulerWedge1_casimir {N : ℕ}
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (Z : Fin N → CubicPolynomial N)
    (hcasimir : ∀ j, ∑ a, eulerWedge1 Z a j * pderiv a F = 0) (j : Fin N) :
    3 * F * Z j = (∑ a, Z a * pderiv a F) * X j := by
  have he := CubicDifferential.euler hF
  simp only [nsmul_eq_mul] at he
  have hs := hcasimir j
  simp only [eulerWedge1, sub_mul, Finset.sum_sub_distrib] at hs
  have hleft : (∑ a, X a * Z j * pderiv a F) = 3 * F * Z j := by
    calc
      _ = (∑ a, X a * pderiv a F) * Z j := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [he]; norm_num
  have hright : (∑ a, X j * Z a * pderiv a F) =
      (∑ a, Z a * pderiv a F) * X j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hleft,hright] at hs
  exact sub_eq_zero.mp hs

/-- The representative-independence calculation of Proposition 2.3:
a projectively zero Euler-wedge bivector annihilating dF is identically zero. -/
theorem eulerWedge1_eq_zero_of_casimir {N : ℕ} (hN : 0 < N)
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (Z : Fin N → CubicPolynomial N)
    (hcasimir : ∀ j, ∑ a, eulerWedge1 Z a j * pderiv a F = 0) :
    eulerWedge1 Z = 0 := by
  funext i j
  exact eulerWedge1_eq_zero_of_radial_relation F _
    (polynomial_ne_zero_of_isolated_gradient hN hgrad) Z
    (radial_relation_of_eulerWedge1_casimir F hF Z hcasimir) i j

/-- Two dF-annihilating representatives differing by an Euler wedge agree. -/
theorem representative_eq_of_eulerWedge1_difference {N : ℕ} (hN : 0 < N)
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (q q' : Fin N → Fin N → CubicPolynomial N) (Z : Fin N → CubicPolynomial N)
    (hq : ∀ j, ∑ a, q a j * pderiv a F = 0)
    (hq' : ∀ j, ∑ a, q' a j * pderiv a F = 0)
    (hdiff : ∀ i j, q i j - q' i j = eulerWedge1 Z i j) : q = q' := by
  have hcasimir (j : Fin N) : ∑ a, eulerWedge1 Z a j * pderiv a F = 0 := by
    simp_rw [← hdiff, sub_mul]
    rw [Finset.sum_sub_distrib, hq, hq', sub_self]
  have hz := eulerWedge1_eq_zero_of_casimir hN F hF hgrad Z hcasimir
  funext i j
  apply sub_eq_zero.mp
  rw [hdiff, hz]
  rfl
/-- Projectively equivalent gradient contractions come from the same
constant trivector. This combines representative independence with the
already established injectivity of gradient contraction. -/
theorem trivector_eq_of_projective_contraction_difference {N : ℕ} (hN : 0 < N)
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (P Q : Trivector N) (Z : Fin N → CubicPolynomial N)
    (hdiff : ∀ i j, contractionCoefficients F P i j - contractionCoefficients F Q i j =
      eulerWedge1 Z i j) : P = Q := by
  apply contraction_injective hF hgrad
  exact representative_eq_of_eulerWedge1_difference hN F hF hgrad
    (contractionCoefficients F P) (contractionCoefficients F Q) Z
    (contraction_gradient_zero F P) (contraction_gradient_zero F Q) hdiff
end NcCubic.Geometry
