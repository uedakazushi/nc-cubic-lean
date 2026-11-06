module
public import NcCubic.Geometry.LocalChartHamiltonian
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}
theorem projectiveChartEquiv_X_val (i : Fin (n+1)) (a : Fin n) :
    (Stacks.ProjectiveChart.chartRingEquiv ℂ i (X a)).val =
      chartCoordinate i (i.succAbove a) := by
  simp [Stacks.ProjectiveChart.chartRingEquiv, Stacks.ProjectiveChart.chartRingEquivDeg0,
    Stacks.ProjectiveChart.chartHom, Stacks.ProjectiveChart.ratio,
    HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', chartCoordinate, chartDenominator]
theorem projectiveChartEquiv_C_val (i : Fin (n+1)) (c : ℂ) :
    (Stacks.ProjectiveChart.chartRingEquiv ℂ i (C c)).val =
      algebraMap ℂ (ChartLocalization i) c := by
  simp [Stacks.ProjectiveChart.chartRingEquiv, Stacks.ProjectiveChart.chartRingEquivDeg0,
    Stacks.ProjectiveChart.chartHom, Stacks.ProjectiveChart.degreeZeroEquiv,
    HomogeneousLocalization.algebraMap_eq, HomogeneousLocalization.fromZeroRingHom]
  change Localization.mk (C c : CubicPolynomial (n+1)) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  exact (IsScalarTower.algebraMap_apply ℂ (CubicPolynomial (n+1)) (ChartLocalization i) c).symm
/-- Every ratio Hamiltonian preserves the actual degree-zero projective chart ring. -/
theorem chartCoordinateHamiltonian_preserves_degreeZero
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i j : Fin (n+1)) (x : ProjectiveChartRing i) :
    ∃ y : ProjectiveChartRing i, y.val = chartCoordinateHamiltonian F P i j x.val := by
  obtain ⟨p, rfl⟩ := (Stacks.ProjectiveChart.chartRingEquiv ℂ i).surjective x
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, ?_⟩
    rw [HomogeneousLocalization.val_zero, projectiveChartEquiv_C_val]
    simp
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    refine ⟨a+b, ?_⟩
    simp only [map_add, HomogeneousLocalization.val_add, ha, hb]
  | mul_X p k hp =>
    obtain ⟨a, ha⟩ := hp
    let e := Stacks.ProjectiveChart.chartRingEquiv ℂ i
    refine ⟨e p * projectiveBracketCoefficient F P hF i j (i.succAbove k) + e (X k) * a, ?_⟩
    simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul,
      map_mul, Derivation.leibniz, smul_eq_mul]
    rw [ha, projectiveBracketCoefficient_matches_hamiltonian, projectiveChartEquiv_X_val]


end NcCubic.Geometry
