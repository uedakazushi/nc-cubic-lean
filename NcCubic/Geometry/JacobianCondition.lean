/-
Coordinate-level Jacobian conditions for the geometric comparison.
These predicates are not definitions of scheme smoothness. The comparison with
AlgebraicGeometry.Smooth on an actual projective hypersurface remains open.
-/
module
public import NcCubic.CubicDifferential
import Mathlib.Tactic.NormNum
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators

/-- The projective Jacobian criterion written on nonzero homogeneous coordinates.
Its equivalence with scheme smoothness is a separate geometric obligation. -/
def ProjectiveJacobianCondition {N : ℕ} (F : CubicPolynomial N) : Prop :=
  ∀ x : CoordinateSpace N, x ≠ 0 → eval x F = 0 →
    ∃ i : Fin N, eval x (pderiv i F) ≠ 0

/-- Euler's equation puts every critical point of a cubic on its zero locus. -/
theorem cubic_zero_of_gradient_zero {N : ℕ} (F : CubicPolynomial N)
    (hF : F.IsHomogeneous 3) (x : CoordinateSpace N)
    (hx : ∀ i, eval x (pderiv i F) = 0) : eval x F = 0 := by
  have he := congrArg (eval x) (CubicDifferential.euler hF)
  simp only [map_sum, map_mul, hx, mul_zero, Finset.sum_const_zero,
    nsmul_eq_mul] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- The isolated-gradient hypothesis is exactly the homogeneous-coordinate
Jacobian condition for a cubic. This does not yet identify it with scheme smoothness. -/
theorem projective_jacobian_iff_isolated_gradient {N : ℕ} (F : CubicPolynomial N)
    (hF : F.IsHomogeneous 3) :
    ProjectiveJacobianCondition F ↔ HasIsolatedGradientZero F := by
  classical
  constructor
  · intro h x hx
    by_contra hne
    obtain ⟨i,hi⟩ := h x hne (cubic_zero_of_gradient_zero F hF x hx)
    exact hi (hx i)
  · intro h x hne hzero
    by_contra! hall
    exact hne (h x hall)

/-- On a standard chart, only the derivatives in its affine directions are needed. -/
def ChartJacobianCondition {N : ℕ} (F : CubicPolynomial N) : Prop :=
  ∀ (i : Fin N) (x : CoordinateSpace N), x i ≠ 0 → eval x F = 0 →
    ∃ j : Fin N, j ≠ i ∧ eval x (pderiv j F) ≠ 0

/-- Euler removes the pivot derivative in the Jacobian test on each chart. -/
theorem chart_jacobian_iff_projective {N : ℕ} (F : CubicPolynomial N)
    (hF : F.IsHomogeneous 3) :
    ChartJacobianCondition F ↔ ProjectiveJacobianCondition F := by
  classical
  constructor
  · intro h x hx hzero
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hall
      apply hx
      funext i
      exact hall i
    obtain ⟨j,hji,hj⟩ := h i x hi hzero
    exact ⟨j,hj⟩
  · intro h i x hxi hzero
    have hx : x ≠ 0 := by
      intro e
      exact hxi (congrFun e i)
    obtain ⟨j,hj⟩ := h x hx hzero
    by_contra! hall
    have he := congrArg (eval x) (CubicDifferential.euler hF)
    simp only [map_sum, map_mul, eval_X, map_nsmul, hzero, nsmul_zero] at he
    have hs : (∑ k, x k * eval x (pderiv k F)) =
        x i * eval x (pderiv i F) := by
      apply Finset.sum_eq_single i
      · intro k hk hki
        rw [hall k hki, mul_zero]
      · simp
    rw [hs] at he
    have hi : eval x (pderiv i F) = 0 := (mul_eq_zero.mp he).resolve_left hxi
    by_cases hji : j = i
    · exact hj (hji ▸ hi)
    · exact hj (hall j hji)

/-- The chart-coordinate Jacobian test implies the exact affine hypothesis used
by the classification library, and conversely. -/
theorem chart_jacobian_iff_isolated_gradient {N : ℕ} (F : CubicPolynomial N)
    (hF : F.IsHomogeneous 3) :
    ChartJacobianCondition F ↔ HasIsolatedGradientZero F :=
  (chart_jacobian_iff_projective F hF).trans (projective_jacobian_iff_isolated_gradient F hF)
end NcCubic.Geometry
