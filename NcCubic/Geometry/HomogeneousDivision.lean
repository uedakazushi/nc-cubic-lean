/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.EulerJacobiLift
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
/-- Projecting a product to the sum of two degrees commutes with its
homogeneous left factor. No domain hypothesis is needed. -/
theorem homogeneousComponent_mul_homogeneous_left {K σ : Type*} [CommRing K]
    {p : MvPolynomial σ K} (q : MvPolynomial σ K) {a b : ℕ} (hp : p.IsHomogeneous a) :
    homogeneousComponent (a+b) (p*q) = p*homogeneousComponent b q := by
  classical
  ext m
  rw [coeff_homogeneousComponent,coeff_mul,coeff_mul]
  by_cases hm : m.degree = a+b
  · simp only [hm,ite_true]
    apply Finset.sum_congr rfl
    intro x hx
    rw [coeff_homogeneousComponent]
    by_cases hi : x.1.degree = a
    · have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hx)
      simp only [map_add] at he
      have hj : x.2.degree = b := by omega
      simp [hj]
    · simp [hp.coeff_eq_zero hi]
  · simp only [hm,ite_false]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [coeff_homogeneousComponent]
    by_cases hi : x.1.degree = a
    · have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hx)
      simp only [map_add] at he
      have hj : x.2.degree ≠ b := by omega
      simp [hj]
    · simp [hp.coeff_eq_zero hi]

/-- Divisibility between homogeneous degrees three and four admits the
canonical degree-one homogeneous quotient. -/
theorem cubic_quartic_quotient {N : ℕ} (F W Q : CubicPolynomial N)
    (hF : F.IsHomogeneous 3) (hW : W.IsHomogeneous 4) (heq : W = F*Q) :
    W = F*homogeneousComponent 1 Q := by
  have h := congrArg (homogeneousComponent 4) heq
  rw [homogeneousComponent_eq_self hW] at h
  exact h.trans (homogeneousComponent_mul_homogeneous_left (b := 1) Q hF)

variable {N : ℕ}
theorem eulerWedge3_isHomogeneous
    (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hd : ∀ i j k, (J i j k).IsHomogeneous 3) (a b c d : Fin N) :
    (eulerWedge3 J a b c d).IsHomogeneous 4 := by
  have hx (i : Fin N) : (X i : CubicPolynomial N).IsHomogeneous 1 := isHomogeneous_X ℂ i
  exact ((((hx a).mul (hd b c d)).sub ((hx b).mul (hd a c d))).add
    ((hx c).mul (hd a b d))).sub ((hx d).mul (hd a b c))

theorem eulerWedge3_swap_first
    (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ a b c, J b a c = -J a b c) (a b c d : Fin N) :
    eulerWedge3 J b a c d = -eulerWedge3 J a b c d := by
  unfold eulerWedge3
  rw [hs a b d,hs a b c]
  ring

/-- Mere coefficientwise divisibility supplies homogeneous quotient data and
the required antisymmetry, using the genuine nonzero cubic equation. -/
theorem exists_euler_quotient (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ a b c, J b a c = -J a b c)
    (hd : ∀ a b c, (J a b c).IsHomogeneous 3)
    (hdiv : ∀ a b c d, F ∣ eulerWedge3 J a b c d) :
    ∃ Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N,
      (∀ a b i j, Q b a i j = -Q a b i j) ∧
      (∀ a b i j, (Q a b i j).IsHomogeneous 1) ∧
      ∀ a b c d, eulerWedge3 J a b c d = F*Q a b c d := by
  classical
  choose Q hQ using hdiv
  let R := fun a b c d => homogeneousComponent 1 (Q a b c d)
  have hR (a b c d : Fin N) : eulerWedge3 J a b c d = F*R a b c d :=
    cubic_quartic_quotient F _ _ hF (eulerWedge3_isHomogeneous J hd a b c d) (hQ a b c d)
  refine ⟨R,?_,?_,hR⟩
  · intro a b i j
    apply mul_left_cancel₀ hF0
    calc
      F*R b a i j = eulerWedge3 J b a i j := (hR b a i j).symm
      _ = -eulerWedge3 J a b i j := eulerWedge3_swap_first J hs a b i j
      _ = F*(-R a b i j) := by rw [hR]; ring
  · intro a b i j
    exact homogeneousComponent_isHomogeneous 1 (Q a b i j)

/-- Full polynomial Jacobi from coefficientwise F divisibility of the Euler
wedge of the actual contraction Jacobiator. All quotient metadata is proved. -/
theorem contraction_jacobi_of_euler_coefficients_divisible (hN : 5 ≤ N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (P : Trivector N)
    (hdiv : ∀ a b c d, F ∣ eulerWedge3 (jacobiArray (contractionCoefficients F P)) a b c d) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) := by
  obtain ⟨Q,hQs,hQd,hQ⟩ := exists_euler_quotient F hF0 hF _
    (jacobiArray_swap_first _ (contraction_skew F P))
    (contraction_jacobiArray_isHomogeneous F P hF) hdiv
  exact contraction_jacobi_of_euler_divisibility hN F hF0 hF hgrad P Q hQs hQd hQ
end NcCubic.Geometry
