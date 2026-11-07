/-
Normal-coordinate brackets of arbitrary skew polynomial coefficients.
The denominator-cleared identity is unconditional; the final divisibility
criterion retains explicit actual localized ideal membership hypotheses.
-/
module
public import NcCubic.Geometry.LocalChartHamiltonian
public import NcCubic.Geometry.LocalizedBracket
public import NcCubic.Geometry.TangentRepresentative
public import NcCubic.Geometry.LocalizedPrincipalIdeal
public import NcCubic.Geometry.ProjectiveEquation
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {N : ℕ}
def normalFraction (F : CubicPolynomial N) (i : Fin N) : ChartLocalization i :=
  IsLocalization.mk' (ChartLocalization i) F (chartDenominator i ^ 3)

lemma normalFraction_eq_projectiveEquation_val (F : CubicPolynomial N)
    (hF : F.IsHomogeneous 3) (i : Fin N) :
    normalFraction F i = (projectiveEquation F hF i).val := by
  change IsLocalization.mk' (ChartLocalization i) F (chartDenominator i ^ 3) =
    Localization.mk F (⟨X i ^ 3, by exact ⟨3,rfl⟩⟩ : Submonoid.powers (X i))
  rw [Localization.mk_eq_mk']
  rfl

lemma normalFraction_clear (F : CubicPolynomial N) (i : Fin N) :
    algebraMap (CubicPolynomial N) (ChartLocalization i) (X i) ^ 3 * normalFraction F i =
      algebraMap (CubicPolynomial N) (ChartLocalization i) F := by
  unfold normalFraction
  rw [← map_pow, mul_comm]
  exact IsLocalization.mk'_spec (ChartLocalization i) F (chartDenominator i ^ 3)

lemma normalFraction_ideal_eq (F : CubicPolynomial N) (i : Fin N) :
    Ideal.span ({normalFraction F i} : Set (ChartLocalization i)) =
      Ideal.span ({algebraMap (CubicPolynomial N) (ChartLocalization i) F} : Set _) := by
  have hu := IsLocalization.map_units (ChartLocalization i) (chartDenominator i)
  change IsUnit (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)) at hu
  rw [← normalFraction_clear F i,
    Ideal.span_singleton_mul_left_unit (hu.pow 3)]

lemma normalRatioBracket_clear (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, q j i = -q i j) (F : CubicPolynomial N) (i j : Fin N) :
    algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)^5 *
      LocalizedPoisson.bracket (Submonoid.powers (X i)) (ChartLocalization i) q
        (normalFraction F i) (chartCoordinate i j) =
    algebraMap (CubicPolynomial N) (ChartLocalization i)
      (eulerWedge1 (gradientContract2 F q) i j - 3*F*q i j) := by
  let t := algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)
  let a := algebraMap (CubicPolynomial N) (ChartLocalization i) (X j)
  let b := algebraMap (CubicPolynomial N) (ChartLocalization i) F
  let f := normalFraction F i
  let r := chartCoordinate i j
  let B := LocalizedPoisson.bracket (Submonoid.powers (X i)) (ChartLocalization i) q
  have hf : t^3*f=b := normalFraction_clear F i
  have hr : t*r=a := by
    simp [t,r,a,chartCoordinate,chartDenominator,mul_comm]
  have hpow : B (t^3) r = 3*t^2*B t r := by
    change LocalizedPoisson.bracket _ _ q _ _ = _
    rw [show t^3=t*t*t by ring]
    simp only [LocalizedPoisson.bracket_mul_left q hq]
    ring
  have h1 := LocalizedPoisson.bracket_mul_right (S:=Submonoid.powers (X i)) q b t r
  have h2 := LocalizedPoisson.bracket_mul_left (S:=Submonoid.powers (X i)) q hq (t^3) f r
  have h3 := LocalizedPoisson.bracket_mul_right (S:=Submonoid.powers (X i)) q t t r
  change B b (t*r) = t*B b r + r*B b t at h1
  change B (t^3*f) r = t^3*B f r + f*B (t^3) r at h2
  change B t (t*r) = t*B t r + r*B t t at h3
  rw [hr] at h1 h3
  rw [hf,hpow] at h2
  have htt : B t t = 0 := LocalizedPoisson.bracket_self q hq t
  rw [htt,mul_zero,add_zero] at h3
  have hbj : B b a = algebraMap _ (ChartLocalization i) (gradientContract2 F q j) := by
    simp [B,b,a,LocalizedPoisson.bracket_algebraMap,bracketFromCoefficients,gradientContract2,Pi.single_apply]
  have hbi : B b t = algebraMap _ (ChartLocalization i) (gradientContract2 F q i) := by
    simp [B,b,t,LocalizedPoisson.bracket_algebraMap,bracketFromCoefficients,gradientContract2,Pi.single_apply]
  have htj : B t a = algebraMap _ (ChartLocalization i) (q i j) := by
    simp [B,t,a,LocalizedPoisson.bracket_algebraMap,bracketFromCoefficients,Pi.single_apply]
  rw [hbj,hbi] at h1
  rw [htj] at h3
  change t^5*B f r = _
  simp only [eulerWedge1,map_sub,map_mul,map_ofNat]
  change t^5*B f r = t*algebraMap _ (ChartLocalization i) (gradientContract2 F q j) -
    a*algebraMap _ (ChartLocalization i) (gradientContract2 F q i) - 3*b*algebraMap _ (ChartLocalization i) (q i j)
  linear_combination -t*h1 - t^2*h2 + 3*f*t^3*h3 -
    3*algebraMap (CubicPolynomial N) (ChartLocalization i) (q i j)*hf -
    algebraMap (CubicPolynomial N) (ChartLocalization i) (gradientContract2 F q i)*hr
lemma eulerTangency_localized_mem
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j, q j i = -q i j)
    (F : CubicPolynomial N) (i j : Fin N)
    (h : LocalizedPoisson.bracket (Submonoid.powers (X i)) (ChartLocalization i) q
      (normalFraction F i) (chartCoordinate i j) ∈
        Ideal.span ({algebraMap (CubicPolynomial N) (ChartLocalization i) F} : Set _)) :
    algebraMap (CubicPolynomial N) (ChartLocalization i)
      (eulerWedge1 (gradientContract2 F q) i j) ∈
        Ideal.span ({algebraMap (CubicPolynomial N) (ChartLocalization i) F} : Set _) := by
  let I := Ideal.span ({algebraMap (CubicPolynomial N) (ChartLocalization i) F} : Set _)
  have hc := Ideal.mul_mem_left I
    (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)^5) h
  rw [normalRatioBracket_clear q hq F i j] at hc
  have hm : algebraMap (CubicPolynomial N) (ChartLocalization i) (3*F*q i j) ∈ I := by
    simp only [map_mul,map_ofNat]
    exact I.mul_mem_right _ (I.mul_mem_left _ (Ideal.subset_span (Set.mem_singleton _)))
  have hadd := I.add_mem hc hm
  simpa only [← map_add, sub_add_cancel] using hadd

lemma eulerTangency_divisible_of_normal_brackets
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j, q j i = -q i j)
    (F : CubicPolynomial N)
    (h : ∀ i j : Fin N,
      LocalizedPoisson.bracket (Submonoid.powers (X i)) (ChartLocalization i) q
        (normalFraction F i) (chartCoordinate i j) ∈
          Ideal.span ({algebraMap (CubicPolynomial N) (ChartLocalization i) F} : Set _)) :
    ∀ i j, F ∣ eulerWedge1 (gradientContract2 F q) i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [eulerWedge1]
  · apply LocalizedPrincipalIdeal.dvd_of_two_localizations i j hij
    · exact eulerTangency_localized_mem q hq F i j (h i j)
    · have hh := eulerTangency_localized_mem q hq F j i (h j i)
      have he : eulerWedge1 (gradientContract2 F q) i j =
          -eulerWedge1 (gradientContract2 F q) j i := by unfold eulerWedge1; ring
      rw [he,map_neg]
      exact neg_mem hh

end NcCubic.Geometry
