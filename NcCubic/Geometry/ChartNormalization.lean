/- Normalizing nonzero homogeneous coordinates on a standard projective chart.
The scaling factor is explicit and no smoothness premise is introduced. -/
module
public import NcCubic.Geometry.ChartCoordinates
public import NcCubic.Geometry.DehomogenizeNonzero
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.ChartComparison
open MvPolynomial
variable {K : Type*} [Field K]

/-- Affine ratios in the chart whose pivot is j. -/
def normalizedCoordinates {n : ℕ} (j : Fin (n+1)) (x : Fin (n+1) → K) : Fin n → K :=
  fun a => (x j)⁻¹ * x (j.succAbove a)

/-- Lifting these ratios rescales the original vector by its inverse pivot. -/
theorem chartLift_normalizedCoordinates {n : ℕ} (j : Fin (n+1))
    (x : Fin (n+1) → K) (hj : x j ≠ 0) :
    chartLift j (normalizedCoordinates j x) = fun k => (x j)⁻¹ * x k := by
  classical
  funext k
  rcases Fin.eq_self_or_eq_succAbove j k with rfl | ⟨a,rfl⟩
  · simp [hj]
  · simp [normalizedCoordinates]

/-- Homogeneous evaluation under normalization has exactly its degree scaling. -/
theorem eval_normalizedCoordinates {n : ℕ} (j : Fin (n+1))
    (x : Fin (n+1) → K) (hj : x j ≠ 0)
    (F : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hF : F.IsHomogeneous d) :
    eval (chartLift j (normalizedCoordinates j x)) F = (x j)⁻¹ ^ d * eval x F := by
  rw [chartLift_normalizedCoordinates j x hj]
  exact AffineChart.eval_scale_of_homogeneous hF _ _

/-- A homogeneous equation has the same zeros after nonzero chart normalization. -/
theorem eval_normalized_zero_iff {n : ℕ} (j : Fin (n+1))
    (x : Fin (n+1) → K) (hj : x j ≠ 0)
    (F : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hF : F.IsHomogeneous d) :
    eval (chartLift j (normalizedCoordinates j x)) F = 0 ↔ eval x F = 0 := by
  rw [eval_normalizedCoordinates j x hj F hF]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero d (inv_ne_zero hj)))

/-- All homogeneous gradient components vanish before normalization iff afterwards. -/
theorem gradient_normalized_zero_iff {n : ℕ} (j : Fin (n+1))
    (x : Fin (n+1) → K) (hj : x j ≠ 0)
    (F : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hF : F.IsHomogeneous d) :
    (∀ k, eval (chartLift j (normalizedCoordinates j x)) (pderiv k F) = 0) ↔
      ∀ k, eval x (pderiv k F) = 0 := by
  apply forall_congr'
  intro k
  exact eval_normalized_zero_iff j x hj _ hF.pderiv

/-- Nonvanishing of some gradient component is also unchanged by normalization. -/
theorem exists_nonzero_gradient_normalized_iff {n : ℕ} (j : Fin (n+1))
    (x : Fin (n+1) → K) (hj : x j ≠ 0)
    (F : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hF : F.IsHomogeneous d) :
    (∃ k, eval (chartLift j (normalizedCoordinates j x)) (pderiv k F) ≠ 0) ↔
      ∃ k, eval x (pderiv k F) ≠ 0 := by
  classical
  simpa only [not_forall] using not_congr (gradient_normalized_zero_iff j x hj F hF)
end NcCubic.Geometry.ChartComparison
