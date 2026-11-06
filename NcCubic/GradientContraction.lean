/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.GradientIndependence
public import NcCubic.ExteriorComparison
@[expose] public section
noncomputable section
namespace NcCubic
open MvPolynomial
open scoped BigOperators

/-- The isolated-gradient condition makes contraction faithful on constant trivectors. -/
theorem contraction_injective {N : ℕ} {F : CubicPolynomial N}
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F) :
    Function.Injective (contractionCoefficients F) := by
  intro P Q h
  apply trivectorCoefficient_ext
  intro i j a
  have hij := congrFun (congrFun h i) j
  have hz : (fun a => trivectorCoefficient P i j a - trivectorCoefficient Q i j a) =
      (0 : CoordinateSpace N) :=
    GradientIndependence.constant_syzygy_zero hF hgrad _ (by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hij)
  exact sub_eq_zero.mp (congrFun hz a)

/-- A nonzero constant trivector cannot have zero contracted bivector. -/
theorem contraction_ne_zero {N : ℕ} {F : CubicPolynomial N}
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    {P : Trivector N} (hP : P ≠ 0) : contractionCoefficients F P ≠ 0 := by
  intro h
  apply hP
  apply contraction_injective hF hgrad
  have hz : contractionCoefficients F (0 : Trivector N) = 0 := by
    funext i j
    simp [contractionCoefficients, trivectorCoefficient]
  rw [hz]
  exact h
end NcCubic
