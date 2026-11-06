/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.ProjectiveBracketDescent
public import NcCubic.Geometry.LocalizedHamiltonianComparison
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}
/-- The full localized bracket preserves the true degree-zero chart ring
in both arbitrary arguments, by polynomial generation of this actual ring. -/
theorem localizedBracket_preserves_degreeZero
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y : ProjectiveChartRing i) :
    ∃ z : ProjectiveChartRing i, z.val =
      LocalizedPoisson.bracket (Submonoid.powers (X i : CubicPolynomial (n+1)))
        (ChartLocalization i) (contractionCoefficients F P) x.val y.val := by
  obtain ⟨p,rfl⟩ := (Stacks.ProjectiveChart.chartRingEquiv ℂ i).surjective x
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0,?_⟩
    rw [HomogeneousLocalization.val_zero,projectiveChartEquiv_C_val]
    simp [LocalizedPoisson.bracket]
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    refine ⟨a+b,?_⟩
    simp only [map_add,HomogeneousLocalization.val_add,ha,hb,LocalizedPoisson.bracket_add_left]
  | mul_X p k hp =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := chartCoordinateHamiltonian_preserves_degreeZero F P hF i (i.succAbove k) y
    let e := Stacks.ProjectiveChart.chartRingEquiv ℂ i
    refine ⟨e p * b + e (X k) * a,?_⟩
    simp only [map_mul,HomogeneousLocalization.val_mul,HomogeneousLocalization.val_add,
      LocalizedPoisson.bracket_mul_left _ (contraction_skew F P)]
    rw [ha,hb,projectiveChartEquiv_X_val,localizedBracket_chartCoordinate]

/-- The actual Poisson bracket on the homogeneous degree-zero chart ring. -/
def projectiveBracket (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y : ProjectiveChartRing i) : ProjectiveChartRing i :=
  (localizedBracket_preserves_degreeZero F P hF i x y).choose

@[simp] theorem projectiveBracket_val
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y : ProjectiveChartRing i) :
    (projectiveBracket F P hF i x y).val =
      LocalizedPoisson.bracket (Submonoid.powers (X i : CubicPolynomial (n+1)))
        (ChartLocalization i) (contractionCoefficients F P) x.val y.val :=
  (localizedBracket_preserves_degreeZero F P hF i x y).choose_spec

theorem projectiveBracket_skew
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y : ProjectiveChartRing i) :
    projectiveBracket F P hF i x y = -projectiveBracket F P hF i y x := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveBracket_val,HomogeneousLocalization.val_neg]
  exact LocalizedPoisson.bracket_skew _ (contraction_skew F P) _ _

theorem projectiveBracket_add_left
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y z : ProjectiveChartRing i) :
    projectiveBracket F P hF i (x+y) z =
      projectiveBracket F P hF i x z + projectiveBracket F P hF i y z := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveBracket_val,HomogeneousLocalization.val_add,LocalizedPoisson.bracket_add_left]

theorem projectiveBracket_add_right
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y z : ProjectiveChartRing i) :
    projectiveBracket F P hF i x (y+z) =
      projectiveBracket F P hF i x y + projectiveBracket F P hF i x z := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveBracket_val,HomogeneousLocalization.val_add,LocalizedPoisson.bracket_add_right]

theorem projectiveBracket_mul_right
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y z : ProjectiveChartRing i) :
    projectiveBracket F P hF i x (y*z) =
      y * projectiveBracket F P hF i x z + z * projectiveBracket F P hF i x y := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveBracket_val,HomogeneousLocalization.val_add,HomogeneousLocalization.val_mul,
    LocalizedPoisson.bracket_mul_right]

theorem projectiveBracket_jacobi
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)))
    (i : Fin (n+1)) (x y z : ProjectiveChartRing i) :
    projectiveBracket F P hF i x (projectiveBracket F P hF i y z) +
    projectiveBracket F P hF i y (projectiveBracket F P hF i z x) +
    projectiveBracket F P hF i z (projectiveBracket F P hF i x y) = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveBracket_val,HomogeneousLocalization.val_add,HomogeneousLocalization.val_zero]
  exact LocalizedPoisson.bracket_jacobi _ (contraction_skew F P) hJac _ _ _
end NcCubic.Geometry
