module
public import NcCubic.Geometry.ProjectiveBracketDescent
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {N : ℕ}
def projectiveEquation (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (i : Fin N) : ProjectiveChartRing i :=
  HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin N) ℂ)
    (isHomogeneous_X ℂ i) 3 F hF
def projectiveQuadraticCoefficient (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (i j k : Fin N) : ProjectiveChartRing i :=
  HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin N) ℂ)
    (isHomogeneous_X ℂ i) 2 (contractionCoefficients F P j k)
    (contractionCoefficients_isHomogeneous F P hF j k)
private theorem fraction_power (i : Fin N) (n : ℕ) (x : CubicPolynomial N) :
    IsLocalization.mk' (ChartLocalization i) x (chartDenominator i ^ n) =
    algebraMap (CubicPolynomial N) (ChartLocalization i) x *
      IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) ^ n := by
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  simpa using IsLocalization.mk'_pow (S := ChartLocalization i) 1 (chartDenominator i) n
private theorem equation_val (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (i : Fin N) :
    (projectiveEquation F hF i).val =
    algebraMap (CubicPolynomial N) (ChartLocalization i) F *
      IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) ^ 3 := by
  change Localization.mk F ⟨X i ^ 3, by exact ⟨3, rfl⟩⟩ = _
  rw [Localization.mk_eq_mk']
  exact fraction_power i 3 F
private theorem quadratic_val (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (i j k : Fin N) :
    (projectiveQuadraticCoefficient F P hF i j k).val =
    algebraMap (CubicPolynomial N) (ChartLocalization i) (contractionCoefficients F P j k) *
      IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) ^ 2 := by
  change Localization.mk (contractionCoefficients F P j k)
    ⟨X i ^ 2, by exact ⟨2, rfl⟩⟩ = _
  rw [Localization.mk_eq_mk']
  exact fraction_power i 2 _
private theorem hamiltonian_inverse (F : CubicPolynomial N) (P : Trivector N) (i j : Fin N) :
    chartCoordinateHamiltonian F P i j
      (IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i)) =
      -(algebraMap (CubicPolynomial N) (ChartLocalization i) (contractionCoefficients F P j i)) *
        IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) ^ 3 := by
  have hdiag : contractionCoefficients F P i i = 0 :=
    CharZero.eq_neg_self_iff.mp (contraction_skew F P i i)
  simp only [chartCoordinateHamiltonian, Derivation.sub_apply, Derivation.smul_apply,
    smul_eq_mul, localizedCoordinateHamiltonian, Derivation.localization_mk',
    Derivation.map_one_eq_zero, mul_zero, zero_sub]
  simp only [show (chartDenominator i : CubicPolynomial N) = X i from rfl,
    polynomialHamiltonian_coordinates, hdiag]
  simp only [← pow_two]
  rw [fraction_power i 2, fraction_power i 2, fraction_power i 2]
  simp only [map_neg, map_zero, mul_zero]
  ring_nf
/-- The normalized defining equation is preserved up to an actual degree-zero multiplier. -/
theorem projectiveEquation_hamiltonian
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3) (i j : Fin N) :
    chartCoordinateHamiltonian F P i j (projectiveEquation F hF i).val =
      ((-3 : ProjectiveChartRing i) * projectiveQuadraticCoefficient F P hF i j i *
        projectiveEquation F hF i).val := by
  have hv3 : (3 : ProjectiveChartRing i).val = 3 := HomogeneousLocalization.val_natCast 3
  rw [equation_val, Derivation.leibniz, chartCoordinateHamiltonian_potential,
    Derivation.leibniz_pow, hamiltonian_inverse]
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_neg, hv3,
    quadratic_val, equation_val, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero]
  ring_nf

/-- The actual principal equation ideal in the degree-zero chart is stable. -/
theorem projectiveEquationIdeal_stable {n : ℕ}
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i j : Fin (n+1)) (x : ProjectiveChartRing i)
    (hx : x ∈ Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i))) :
    ∃ y : ProjectiveChartRing i,
      y ∈ Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i)) ∧
      y.val = chartCoordinateHamiltonian F P i j x.val := by
  rw [Ideal.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨da, hda⟩ := chartCoordinateHamiltonian_preserves_degreeZero F P hF i j a
  let c : ProjectiveChartRing i := -3 * projectiveQuadraticCoefficient F P hF i j i
  refine ⟨projectiveEquation F hF i * (da + c*a), ?_, ?_⟩
  · rw [Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  · simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_add,
      Derivation.leibniz, smul_eq_mul]
    rw [← hda, projectiveEquation_hamiltonian]
    simp only [HomogeneousLocalization.val_mul, c]
    ring_nf

end NcCubic.Geometry
