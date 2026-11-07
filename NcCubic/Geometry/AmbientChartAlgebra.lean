/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.AmbientProjectiveRelative
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 600000
variable {n : ℕ}

/-- The polynomial chart isomorphism respects the actual coefficients pulled
back along the genuine projective-space structure morphism. -/
theorem ambientSectionsChartEquiv_C (i : Fin (n+1)) (c : ℂ) :
    Stacks.ProjectiveChart.sectionsChartEquiv ℂ i (C c) =
      AffineSmoothness.coefficientMap
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
        (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)) c := by
  rw [homogeneous_coefficientMap_eq_constant (by omega) (isHomogeneous_X ℂ i)]
  change homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
      (Stacks.ProjectiveChart.chartRingEquiv ℂ i (C c)) =
    homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
      (HomogeneousBasic.constant (isHomogeneous_X ℂ i) c)
  apply congrArg (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega))
  apply HomogeneousLocalization.val_injective
  rw [projectiveChartEquiv_C_val,HomogeneousBasic.constant_val]
  simpa only [MvPolynomial.algebraMap_eq] using
    (IsScalarTower.algebraMap_apply ℂ (CubicPolynomial (n+1)) (ChartLocalization i) c)

/-- The actual projective chart section ring is a polynomial algebra over ℂ,
with scalar structure specified by the genuine scheme morphism. -/
def ambientSectionsChartAlgEquiv (i : Fin (n+1)) :
    letI : Algebra ℂ Γ(ProjectiveAmbient n,
      Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)) :=
      (AffineSmoothness.coefficientMap
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
        (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))).toAlgebra
    MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] Γ(ProjectiveAmbient n,
      Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)) := by
  letI : Algebra ℂ Γ(ProjectiveAmbient n,
      Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)) :=
      (AffineSmoothness.coefficientMap
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
        (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))).toAlgebra
  refine {toRingEquiv := Stacks.ProjectiveChart.sectionsChartEquiv ℂ i,commutes' := ?_}
  intro c
  exact ambientSectionsChartEquiv_C i c
end NcCubic.Geometry
