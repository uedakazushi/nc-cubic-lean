/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Faithfulness from coefficientwise vanishing of projective standard representatives. -/
module
public import NcCubic.Geometry.HomogeneousDivision
public import NcCubic.Geometry.RepresentativeUniqueness
@[expose] public noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
variable {N : ℕ}

/-- Coefficientwise vanishing on the cubic of the projectivized standard
representative forces its polynomial representative to vanish. -/
theorem contraction_zero_of_euler_coefficients_divisible (hN : 5 ≤ N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (P : Trivector N)
    (hdiv : ∀ i j k, F ∣ eulerWedge2 (contractionCoefficients F P) i j k) :
    contractionCoefficients F P = 0 := by
  classical
  let q := contractionCoefficients F P
  choose Q hQ using hdiv
  let T := fun i j k => homogeneousComponent 0 (Q i j k)
  have hT (i j k) : eulerWedge2 q i j k = F*T i j k := by
    have hd : (eulerWedge2 q i j k).IsHomogeneous 3 := by
      exact (((isHomogeneous_X ℂ i).mul (contractionCoefficients_isHomogeneous F P hF j k)).sub
        ((isHomogeneous_X ℂ j).mul (contractionCoefficients_isHomogeneous F P hF i k))).add
        ((isHomogeneous_X ℂ k).mul (contractionCoefficients_isHomogeneous F P hF i j))
    have hh := congrArg (homogeneousComponent 3) (hQ i j k)
    rw [homogeneousComponent_eq_self hd] at hh
    exact hh.trans (homogeneousComponent_mul_homogeneous_left (b := 0) _ hF)
  have hTd (a i j k) : pderiv a (T i j k) = 0 := by
    simp only [T,homogeneousComponent_zero,pderiv_C]
  have hg (i j) : gradientContract3 F T i j = 3 * q i j := by
    apply mul_left_cancel₀ hF0
    have hc := gradientContract3_eulerWedge2 F hF q (contraction_gradient_zero F P) i j
    simp only [gradientContract3] at hc ⊢
    simp_rw [hT] at hc
    calc
      F * (∑ a, pderiv a F * T a i j) = ∑ a, pderiv a F * (F*T a i j) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      _ = 3*F*q i j := hc
      _ = F*(3*q i j) := by ring
  have hd (i j) : divergence3 (eulerWedge2 q) i j = gradientContract3 F T i j := by
    simp only [divergence3,gradientContract3]
    simp_rw [hT,pderiv_mul,hTd,mul_zero,add_zero]
  funext i j
  have h := divergence3_eulerWedge2 q (contraction_skew F P)
    (contractionCoefficients_isHomogeneous F P hF) i j
  rw [hd,hg] at h
  have hz : eulerWedge1 (divergence2 q) i j = 0 := by
    simp only [eulerWedge1,q,divergence2_contraction,mul_zero,sub_zero]
  rw [hz,sub_zero,nsmul_eq_mul] at h
  have hn : (N : ℂ) - 3 ≠ 0 := by
    have : (3 : ℕ) < N := by omega
    exact sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt this))
  have hp : C ((N : ℂ)-3) * q i j = 0 := by
    simp only [map_sub,map_natCast,map_ofNat] at *
    linear_combination -h
  exact (mul_eq_zero.mp hp).resolve_left (by exact fun hc => hn ((MvPolynomial.C_injective (Fin N) ℂ) (hc.trans (map_zero _).symm)))

/-- Faithfulness of a standard representative under coefficientwise vanishing
of its projectivization on the genuine cubic equation. -/
theorem trivector_zero_of_euler_coefficients_divisible (hN : 5 ≤ N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (P : Trivector N)
    (hdiv : ∀ i j k, F ∣ eulerWedge2 (contractionCoefficients F P) i j k) : P = 0 := by
  apply contraction_injective hF hgrad
  have hz := contraction_zero_of_euler_coefficients_divisible hN F hF0 hF P hdiv
  rw [hz]
  funext i j
  simp [contractionCoefficients, trivectorCoefficient]
end NcCubic.Geometry
