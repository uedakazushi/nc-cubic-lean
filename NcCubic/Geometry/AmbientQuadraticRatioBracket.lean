/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.LocalizedPairBracket
public import NcCubic.Geometry.AmbientProjectiveBiderivation
public import NcCubic.Geometry.ChartJacobiDivisibility
public import NcCubic.Geometry.QuadraticCoefficientRatio
public import NcCubic.Geometry.CanonicalQuadraticRatioBracket
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry.AmbientQuadraticRatioBracket
open ProjectiveCoordinateDerivatives
open QuadraticCoefficientRatio CanonicalEulerCoordinateEvaluation
open scoped BigOperators
variable {n : ℕ}

/-- Basis evaluation of the actual glued biderivation. -/
theorem ambient_biderivation_on_basis
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (hskew : ∀ i j, q j i = -q i j)
    (s : PositiveBasicIndex n) (a b : Γ(ProjectiveAmbient n,positiveBasicOpen s)) :
    (ambientProjectiveBiderivation q hq hskew).bracket (positiveBasicOpen s) a b =
      HomogeneousSections.bracket q hq s.1.pos s.2.property a b := by
  have h := (ambientBasisBiderivation q hq hskew).glued_restrict
    (positiveBasicOpen s) a b s le_rfl
  have hid : (homOfLE (le_rfl : positiveBasicOpen s ≤ positiveBasicOpen s)).op =
      𝟙 (op (positiveBasicOpen s)) := Subsingleton.elim _ _
  rw [hid, CategoryTheory.Functor.map_id] at h
  change (ambientBasisBiderivation q hq hskew).glued.bracket _ a b =
    (ambientBasisBiderivation q hq hskew).bracket s a b
  simpa only [ConcreteCategory.id_apply] using h

theorem ambient_biderivation_chart_equiv
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (hskew : ∀ i j, q j i = -q i j)
    (i : Fin (n+1)) (a b : ProjectiveChartRing i) :
    (ambientProjectiveBiderivation q hq hskew).bracket (coordinateOpen i)
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos a)
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos b) =
    homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos
      (HomogeneousBasic.bracket q hq Nat.one_pos (isHomogeneous_X ℂ i) a b) := by
  let s : PositiveBasicIndex n := ⟨⟨1,Nat.one_pos⟩,⟨X i,isHomogeneous_X ℂ i⟩⟩
  exact (ambient_biderivation_on_basis q hq hskew s _ _).trans
    (HomogeneousSections.bracket_equiv q hq Nat.one_pos (isHomogeneous_X ℂ i) a b)

/-- The degree-zero homogeneous chart version of the coordinate field value. -/
def homogeneousFieldValue (i j l : Fin (n+1)) : ProjectiveChartRing i :=
  (if j=l then 1 else 0) - Stacks.ProjectiveChart.ratio ℂ i l * (if j=i then 1 else 0)

theorem homogeneousFieldValue_val (i j l : Fin (n+1)) :
    (homogeneousFieldValue i j l).val = LocalizedPairBracket.ratioFieldValue i j l := by
  classical
  have hdelta (a b : Fin (n+1)) :
      HomogeneousLocalization.val (if a=b then (1 : ProjectiveChartRing i) else 0) =
        (if a=b then (1 : ChartLocalization i) else 0) := by
    by_cases h : a = b
    · simp only [ite_eq_left h, HomogeneousLocalization.val_one]
    · simp only [ite_eq_right h, HomogeneousLocalization.val_zero]
  unfold homogeneousFieldValue LocalizedPairBracket.ratioFieldValue
  rw [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
    projectiveRatio_val, hdelta, hdelta]


/-- Clear the actual quadratic fraction's denominator. -/
theorem quadraticChartFraction_clear
    (c : homogeneousSubmodule (Fin (n+1)) ℂ 2) (i : Fin (n+1)) :
    algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) (X i)^2 *
      (quadraticChartFraction c i).val =
      algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) c := by
  unfold quadraticChartFraction
  rw [HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk', ← map_pow, mul_comm]
  exact IsLocalization.mk'_spec (ChartLocalization i) (c : CubicPolynomial (n+1))
    (⟨X i ^ 2, by exact ⟨2,rfl⟩⟩ : Submonoid.powers (X i))

/-- Ordered coordinate-pair evaluation as an equality in the genuine degree-zero chart ring. -/
theorem homogeneous_pair_ratio_bracket {κ : Type*} [Fintype κ]
    (idx : κ → Fin 2 → Fin (n+1)) (c : κ → homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i l m : Fin (n+1)) :
    HomogeneousBasic.bracket (pairCoefficients idx (fun s => (c s : CubicPolynomial (n+1))))
      (pairCoefficients_homogeneous idx _ 2 (fun s => (c s).property))
      Nat.one_pos (isHomogeneous_X ℂ i)
      (Stacks.ProjectiveChart.ratio ℂ i l) (Stacks.ProjectiveChart.ratio ℂ i m) =
    ∑ s, quadraticChartFraction (c s) i *
      (homogeneousFieldValue i (idx s 0) l * homogeneousFieldValue i (idx s 1) m -
        homogeneousFieldValue i (idx s 1) l * homogeneousFieldValue i (idx s 0) m) := by
  apply HomogeneousLocalization.val_injective
  change algebraMap (ProjectiveChartRing i) (ChartLocalization i) _ =
    algebraMap (ProjectiveChartRing i) (ChartLocalization i) _
  simp only [map_sum, map_mul, map_sub]
  simp only [HomogeneousLocalization.algebraMap_apply, HomogeneousBasic.bracket_val,
    projectiveRatio_val, homogeneousFieldValue_val]
  have ht : IsUnit (algebraMap (CubicPolynomial (n+1)) (ChartLocalization i) (X i)) :=
    IsLocalization.map_units (ChartLocalization i) (chartDenominator i)
  apply (ht.pow 2).mul_left_cancel
  rw [LocalizedPairBracket.ratio_bracket_pairCoefficients_clear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← mul_assoc, quadraticChartFraction_clear]
/-- The actual canonical chart ring map followed by an actual open restriction. -/
def chartSectionMap (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ coordinateOpen i) : ProjectiveChartRing i →+* Γ(ProjectiveAmbient n,U) :=
  ((ProjectiveAmbient n).presheaf.map (homOfLE hU).op).hom.comp
    (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos).toRingHom

@[simp] theorem chartSectionMap_ratio (i l : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ coordinateOpen i) :
    chartSectionMap i U hU (Stacks.ProjectiveChart.ratio ℂ i l) = restrictedRatio i l U hU := rfl

@[simp] theorem chartSectionMap_quadratic (c : homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) :
    chartSectionMap i U hU (quadraticChartFraction c i) = ratioQuadratic c i U hU := rfl

theorem chartSectionMap_field (i j l : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ coordinateOpen i) :
    chartSectionMap i U hU (homogeneousFieldValue i j l) = chartFieldValue i j l U hU := by
  classical
  have hdelta (a b : Fin (n+1)) :
      chartSectionMap i U hU (if a=b then (1 : ProjectiveChartRing i) else 0) =
        (if a=b then (1 : Γ(ProjectiveAmbient n,U)) else 0) := by
    by_cases h : a = b
    · simp only [ite_eq_left h, map_one]
    · simp only [ite_eq_right h, map_zero]
  unfold homogeneousFieldValue chartFieldValue
  rw [map_sub, map_mul, chartSectionMap_ratio, hdelta, hdelta]

/-- The actual homogeneous quadratic biderivation, evaluated on genuine ratio
sections of ANY subopen of a coordinate chart, has the ordered-pair determinant
formula with the canonical quadratic coefficient c/Xi². -/
theorem ambient_pair_ratio_bracket {κ : Type*} [Fintype κ]
    (idx : κ → Fin 2 → Fin (n+1)) (c : κ → homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i l m : Fin (n+1)) (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) :
    (ambientProjectiveBiderivation
      (pairCoefficients idx (fun s => (c s : CubicPolynomial (n+1))))
      (pairCoefficients_homogeneous idx _ 2 (fun s => (c s).property))
      (pairCoefficients_skew idx _)).bracket U
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
    ∑ s, ratioQuadratic (c s) i U hU *
      (chartFieldValue i (idx s 0) l U hU * chartFieldValue i (idx s 1) m U hU -
        chartFieldValue i (idx s 1) l U hU * chartFieldValue i (idx s 0) m U hU) := by
  let q := pairCoefficients idx (fun s => (c s : CubicPolynomial (n+1)))
  let hq : ∀ j k, (q j k).IsHomogeneous 2 :=
    pairCoefficients_homogeneous idx _ 2 (fun s => (c s).property)
  let hs : ∀ j k, q k j = -q j k := pairCoefficients_skew idx _
  let B := ambientProjectiveBiderivation q hq hs
  have hb := ambient_biderivation_chart_equiv q hq hs i
    (Stacks.ProjectiveChart.ratio ℂ i l) (Stacks.ProjectiveChart.ratio ℂ i m)
  have hn := B.restrict hU (coordinateRatio i l) (coordinateRatio i m)
  have he : B.bracket U (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
      chartSectionMap i U hU
        (HomogeneousBasic.bracket q hq Nat.one_pos (isHomogeneous_X ℂ i)
          (Stacks.ProjectiveChart.ratio ℂ i l) (Stacks.ProjectiveChart.ratio ℂ i m)) :=
    hn.symm.trans (congrArg (((ProjectiveAmbient n).presheaf.map (homOfLE hU).op).hom) hb)
  change B.bracket U (restrictedRatio i l U hU) (restrictedRatio i m U hU) = _
  rw [he, homogeneous_pair_ratio_bracket]
  simp only [map_sum, map_mul, map_sub, chartSectionMap_quadratic, chartSectionMap_field]
end NcCubic.Geometry.AmbientQuadraticRatioBracket
