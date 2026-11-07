module
public import NcCubic.Geometry.HypersurfaceStandardComparison
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

theorem projectiveBracket_ratios
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i j k : Fin (n+1)) :
    projectiveBracket F P hF i (Stacks.ProjectiveChart.ratio ℂ i j)
      (Stacks.ProjectiveChart.ratio ℂ i k) = projectiveBracketCoefficient F P hF i j k := by
  apply HomogeneousLocalization.val_injective
  rw [projectiveBracket_val,projectiveRatio_val,projectiveRatio_val,
    localizedBracket_chartCoordinate,projectiveBracketCoefficient_matches_hamiltonian]

theorem eulerWedge2_contraction_eq_ratioNumerator
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (i j k : Fin (n+1)) :
    eulerWedge2 (contractionCoefficients F P) i j k = ratioBracketNumerator F P i j k := by
  rw [eulerWedge2,ratioBracketNumerator,contraction_skew F P j i]
  ring

theorem projectiveCoefficient_mem_equationIdeal_of_global_zero
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hzero : ∀ (U : Z.Opens) (a b : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b = 0)
    (i j k : Fin (n+1)) : projectiveBracketCoefficient F P hF i j k ∈
      Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i)) := by
  let E := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos
  let r := Stacks.ProjectiveChart.ratio ℂ i
  have hz := hzero _ ((ι.app _).hom (E (r j))) ((ι.app _).hom (E (r k)))
  rw [hypersurfaceGlobalBracket_standard_pullback,projectiveSectionBracket_equiv,
    projectiveBracket_ratios] at hz
  let e := projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply e.injective
  rw [map_zero]
  exact (projectiveHypersurfaceChartSectionsEquiv_mk ι F hF hideal i _).trans hz

theorem eulerWedge2_localized_mem_of_global_zero
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hzero : ∀ (U : Z.Opens) (a b : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b = 0)
    (i j k : Fin (n+1)) :
    algebraMap (CubicPolynomial (n+1)) (ChartLocalization i)
      (eulerWedge2 (contractionCoefficients F P) i j k) ∈
      Ideal.span ({algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) F} : Set (ChartLocalization i)) := by
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton.mp
    (projectiveCoefficient_mem_equationIdeal_of_global_zero ι F P hF hideal hzero i j k)
  have hv := congrArg HomogeneousLocalization.val ha
  have hs : (algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) (X i))^3 *
      (projectiveEquation F hF i).val = algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) F := by
    change _ * Localization.mk F (⟨(X i)^3,by exact ⟨3,rfl⟩⟩ : Submonoid.powers (X i)) = _
    rw [Localization.mk_eq_mk']
    have hh := IsLocalization.mk'_spec (ChartLocalization i) F
      (⟨(X i)^3,by exact ⟨3,rfl⟩⟩ : Submonoid.powers (X i))
    rw [map_pow] at hh
    exact (mul_comm _ _).trans hh
  have hc : (algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) (X i))^3 *
      (projectiveBracketCoefficient F P hF i j k).val =
      algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) (ratioBracketNumerator F P i j k) := by
    rw [projectiveBracketCoefficient_val]
    have hh := IsLocalization.mk'_spec (ChartLocalization i) (ratioBracketNumerator F P i j k)
      (chartDenominator i ^ 3)
    change IsLocalization.mk' (ChartLocalization i) (ratioBracketNumerator F P i j k)
      (chartDenominator i ^ 3) * algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) ((X i)^3) = _ at hh
    rw [map_pow] at hh
    exact (mul_comm _ _).trans hh
  apply Ideal.mem_span_singleton.mpr
  refine ⟨a.val,?_⟩
  rw [eulerWedge2_contraction_eq_ratioNumerator,← hc,← hs]
  rw [HomogeneousLocalization.val_mul] at hv
  rw [hv]
  ring

/-- A genuinely zero hypersurface operation forces coefficientwise equation
divisibility of the projective bivector numerator. -/
theorem eulerWedge2_divisible_of_hypersurfaceGlobalBracket_zero
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hzero : ∀ (U : Z.Opens) (a b : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b = 0) :
    ∀ i j k, F ∣ eulerWedge2 (contractionCoefficients F P) i j k := by
  intro i j k
  have hs : eulerWedge2 (contractionCoefficients F P) j i k =
      -eulerWedge2 (contractionCoefficients F P) i j k := by
    unfold eulerWedge2
    rw [contraction_skew F P i j]
    ring
  by_cases hij : i = j
  · subst j
    have hz : eulerWedge2 (contractionCoefficients F P) i i k = 0 := by
      have hh : (2 : CubicPolynomial (n+1))*eulerWedge2 (contractionCoefficients F P) i i k = 0 := by
        linear_combination hs
      exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
    rw [hz]
    exact dvd_zero F
  · apply LocalizedPrincipalIdeal.dvd_of_two_localizations i j hij F _
      (eulerWedge2_localized_mem_of_global_zero ι F P hF hideal hzero i j k)
    have hm := eulerWedge2_localized_mem_of_global_zero ι F P hF hideal hzero j i k
    rw [hs,map_neg] at hm
    exact (Ideal.neg_mem_iff _).mp hm
end NcCubic.Geometry
