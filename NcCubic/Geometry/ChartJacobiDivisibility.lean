module
public import NcCubic.Geometry.RatioJacobi
public import NcCubic.Geometry.HomogeneousDivision
public import NcCubic.Geometry.LocalizedPrincipalIdeal
public import NcCubic.Geometry.ProjectiveHypersurfacePoisson
@[expose] public section
noncomputable section

namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem projectiveRatio_val (i j : Fin (n+1)) :
    (Stacks.ProjectiveChart.ratio ℂ i j).val = chartCoordinate i j := by
  simp [Stacks.ProjectiveChart.ratio, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk',chartCoordinate,chartDenominator]

theorem eulerJacobi_localized_mem
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i j k l : Fin (n+1))
    (hJac : ∀ a b c : ProjectiveHypersurfaceChartRing F hF i,
      projectiveHypersurfaceBracket F P hF i a (projectiveHypersurfaceBracket F P hF i b c) +
      projectiveHypersurfaceBracket F P hF i b (projectiveHypersurfaceBracket F P hF i c a) +
      projectiveHypersurfaceBracket F P hF i c (projectiveHypersurfaceBracket F P hF i a b) = 0) :
    algebraMap (CubicPolynomial (n+1)) (ChartLocalization i)
      (eulerWedge3 (jacobiArray (contractionCoefficients F P)) i j k l) ∈
      Ideal.span ({algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) F} : Set (ChartLocalization i)) := by
  let I := Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i))
  let r := Stacks.ProjectiveChart.ratio ℂ i
  let B := projectiveBracket F P hF i
  let J := B (r j) (B (r k) (r l)) + B (r k) (B (r l) (r j)) + B (r l) (B (r j) (r k))
  have hm : J ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := hJac (Ideal.Quotient.mk I (r j)) (Ideal.Quotient.mk I (r k))
      (Ideal.Quotient.mk I (r l))
    dsimp [I] at hh ⊢
    simpa only [projectiveHypersurfaceBracket_mk,← map_add] using hh
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp hm
  have hv := congrArg HomogeneousLocalization.val ha
  have hj : LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i))
      (contractionCoefficients F P) (chartCoordinate i j) (chartCoordinate i k) (chartCoordinate i l) =
      (projectiveEquation F hF i).val*a.val := by
    simpa only [J,B,r,HomogeneousLocalization.val_add,HomogeneousLocalization.val_mul,
      projectiveBracket_val,projectiveRatio_val,LocalizedPoisson.jacobiator] using hv
  have hs : (algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) (X i))^3 *
      (projectiveEquation F hF i).val = algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) F := by
    change _ * Localization.mk F (⟨(X i)^3,by exact ⟨3,rfl⟩⟩ : Submonoid.powers (X i)) = _
    rw [Localization.mk_eq_mk']
    have hs0 := IsLocalization.mk'_spec (ChartLocalization i) F
      (⟨(X i)^3,by exact ⟨3,rfl⟩⟩ : Submonoid.powers (X i))
    rw [map_pow] at hs0
    exact (mul_comm _ _).trans hs0
  apply Ideal.mem_span_singleton.mpr
  refine ⟨algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) (X i)*a.val,?_⟩
  rw [← ratioJacobi_eulerWedge _ (contraction_skew F P),hj,← hs]
  ring

/-- Jacobi on the actual hypersurface quotient charts forces the full
ambient polynomial Jacobi identity. -/
theorem polynomialJacobi_of_hypersurfaceChartJacobi
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F) (P : Trivector (n+1))
    (hJac : ∀ i (a b c : ProjectiveHypersurfaceChartRing F hF i),
      projectiveHypersurfaceBracket F P hF i a (projectiveHypersurfaceBracket F P hF i b c) +
      projectiveHypersurfaceBracket F P hF i b (projectiveHypersurfaceBracket F P hF i c a) +
      projectiveHypersurfaceBracket F P hF i c (projectiveHypersurfaceBracket F P hF i a b) = 0) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) := by
  apply contraction_jacobi_of_euler_coefficients_divisible hN F hF0 hF hgrad P
  intro a b c d
  have hs := eulerWedge3_swap_first (jacobiArray (contractionCoefficients F P))
    (jacobiArray_swap_first _ (contraction_skew F P)) a b c d
  by_cases hab : a = b
  · subst b
    have hz : eulerWedge3 (jacobiArray (contractionCoefficients F P)) a a c d = 0 := by
      have hh : (2 : CubicPolynomial (n+1)) *
          eulerWedge3 (jacobiArray (contractionCoefficients F P)) a a c d = 0 := by
        linear_combination hs
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
    rw [hz]
    exact dvd_zero F
  · apply LocalizedPrincipalIdeal.dvd_of_two_localizations a b hab F _
      (eulerJacobi_localized_mem F P hF a b c d (hJac a))
    have hb := eulerJacobi_localized_mem F P hF b a c d (hJac b)
    rw [hs,map_neg] at hb
    exact (Ideal.neg_mem_iff _).mp hb
end NcCubic.Geometry
