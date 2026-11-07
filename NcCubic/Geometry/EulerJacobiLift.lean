/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.JacobiHomogeneity
public import NcCubic.GradientIndependence
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- Exterior product of the Euler field with a polynomial trivector. -/
def eulerWedge3 (J : Fin N → Fin N → Fin N → CubicPolynomial N) (i j k l : Fin N) :=
  X i * J j k l - X j * J i k l + X k * J i j l - X l * J i j k

def divergence4 (Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N)
    (i j k : Fin N) := ∑ a, pderiv a (Q a i j k)

def gradientContract4 (F : CubicPolynomial N)
    (Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N) (i j k : Fin N) :=
  ∑ a, pderiv a F * Q a i j k

/-- The Euler/divergence anticommutator in the cubic trivector strand. -/
theorem divergence4_eulerWedge3
    (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ i j k, J j i k = -J i j k)
    (hc : ∀ i j k, J j k i = J i j k)
    (hd : ∀ i j k, (J i j k).IsHomogeneous 3) (i j k : Fin N) :
    divergence4 (eulerWedge3 J) i j k = N • J i j k - eulerWedge2 (divergence3 J) i j k := by
  classical
  simp only [divergence4, eulerWedge3, map_add, map_sub, pderiv_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [pderiv_X_self, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have he : (∑ a, X a * pderiv a (J i j k)) = 3 • J i j k := (hd i j k).sum_X_mul_pderiv
  have ha (u v w : Fin N) : (∑ a, pderiv a (X u) * J a v w) = J u v w := by
    simp [pderiv_X, Pi.single_apply]
  rw [he, ha, ha, ha, hs i j k, hc j k i, hc i j k]
  simp only [divergence3, eulerWedge2, Finset.mul_sum, nsmul_eq_mul]
  ring

/-- A horizontal trivector contracts its Euler wedge to three times F. -/
theorem gradientContract4_eulerWedge3 (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hh : ∀ i j, gradientContract3 F J i j = 0) (i j k : Fin N) :
    gradientContract4 F (eulerWedge3 J) i j k = 3 * F * J i j k := by
  simp only [gradientContract4, eulerWedge3, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he : (∑ a, pderiv a F * (X a * J i j k)) = 3*F*J i j k := by
    calc
      _ = (∑ a, X a*pderiv a F)*J i j k := by
        simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; ring
      _ = _ := by rw [hF.sum_X_mul_pderiv]; simp [nsmul_eq_mul]
  have hz (u v w : Fin N) : (∑ a, pderiv a F * (X u * J a v w)) = 0 := by
    calc
      _ = X u * gradientContract3 F J v w := by
        simp only [gradientContract3, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _; ring
      _ = 0 := by rw [hh, mul_zero]
  rw [he,hz,hz,hz,sub_zero,add_zero,sub_zero]

theorem divergence4_mul (F : CubicPolynomial N)
    (Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N) (i j k : Fin N) :
    divergence4 (fun a b c d => F*Q a b c d) i j k =
      gradientContract4 F Q i j k + F*divergence4 Q i j k := by
  simp [divergence4,gradientContract4,Finset.sum_add_distrib,Finset.mul_sum,mul_comm,add_comm]

theorem gradientContract4_mul (F c : CubicPolynomial N)
    (Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N) (i j k : Fin N) :
    gradientContract4 F (fun a b d e => c*Q a b d e) i j k =
      c*gradientContract4 F Q i j k := by
  simp [gradientContract4,Finset.mul_sum,mul_left_comm]

/-- Divergence anticommutes with gradient contraction; Hessian terms cancel
against alternation in the two contracted indices. -/
theorem divergence3_gradientContract4 (F : CubicPolynomial N)
    (Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ a b i j, Q b a i j = -Q a b i j) (i j : Fin N) :
    divergence3 (gradientContract4 F Q) i j = -gradientContract3 F (divergence4 Q) i j := by
  have hA : (∑ b, ∑ a, pderiv b (pderiv a F) * Q a b i j) = 0 := by
    apply CharZero.eq_neg_self_iff.mp
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    rw [hs, pderiv_comm]
    ring
  have hB : (∑ b, ∑ a, pderiv a F * pderiv b (Q a b i j)) =
      -gradientContract3 F (divergence4 Q) i j := by
    rw [Finset.sum_comm]
    simp only [gradientContract3,divergence4,Finset.mul_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hs b a i j, map_neg]
    ring
  simp only [divergence3,gradientContract4,map_sum,pderiv_mul,
    Finset.sum_add_distrib]
  linear_combination hA + hB

/-- A homogeneous degree-zero polynomial array with zero gradient contraction
is zero, by the genuine isolated-gradient hypothesis. -/
theorem constant_trivector_array_zero (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F)
    (R : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hdegree : ∀ a i j, (R a i j).IsHomogeneous 0)
    (hh : ∀ i j, gradientContract3 F R i j = 0) (a i j : Fin N) : R a i j = 0 := by
  have hc (a i j : Fin N) : C ((R a i j).coeff 0) = R a i j := by
    rw [← homogeneousComponent_zero, homogeneousComponent_eq_self (hdegree a i j)]
  have hz := GradientIndependence.constant_syzygy_zero hF hgrad
    (fun b => (R b i j).coeff 0) (by
      simp_rw [hc]
      simpa only [gradientContract3,mul_comm] using hh i j)
  have hz' := congrFun hz a
  rw [← hc, hz']
  simp

/-- A closed horizontal cubic trivector vanishes if its Euler wedge is
F times a linear four-array skew in its first two indices. The geometric divisibility remains
an explicit hypothesis; no cohomology lift is assumed here. -/
theorem euler_divisibility_lift_vanishes (hN : 5 ≤ N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F)
    (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hJs : ∀ i j k, J j i k = -J i j k)
    (hJc : ∀ i j k, J j k i = J i j k)
    (hJd : ∀ i j k, (J i j k).IsHomogeneous 3)
    (hclosed : ∀ i j, divergence3 J i j = 0)
    (hhorizontal : ∀ i j, gradientContract3 F J i j = 0)
    (Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N)
    (hQs : ∀ a b i j, Q b a i j = -Q a b i j)
    (hQd : ∀ a b i j, (Q a b i j).IsHomogeneous 1)
    (heq : ∀ a b c d, eulerWedge3 J a b c d = F * Q a b c d)
    (i j k : Fin N) : J i j k = 0 := by
  have hE : eulerWedge3 J = fun a b c d => F*Q a b c d := by
    funext a b c d
    exact heq a b c d
  have hG (i j k : Fin N) : gradientContract4 F Q i j k = 3*J i j k := by
    have hh := gradientContract4_eulerWedge3 F hF J hhorizontal i j k
    rw [hE,gradientContract4_mul] at hh
    apply mul_left_cancel₀ hF0
    calc
      _ = 3*F*J i j k := hh
      _ = _ := by ring
  have hRdeg (a i j : Fin N) : (divergence4 Q a i j).IsHomogeneous 0 := by
    apply IsHomogeneous.sum
    intro b _
    simpa using (hQd b a i j).pderiv (i := b)
  have hthree (a : Fin N) : pderiv a (3 : CubicPolynomial N) = 0 := by
    have h := (pderiv a : Derivation ℂ (CubicPolynomial N) (CubicPolynomial N)).map_natCast 3
    norm_num at h
    exact h
  have hRhor (i j : Fin N) : gradientContract3 F (divergence4 Q) i j = 0 := by
    have hh : divergence3 (gradientContract4 F Q) i j = 0 := by
      calc
        _ = 3 * divergence3 J i j := by
          simp [divergence3,hG,Finset.mul_sum,hthree]
        _ = 0 := by rw [hclosed,mul_zero]
    rw [divergence3_gradientContract4 F Q hQs] at hh
    exact neg_eq_zero.mp hh
  have hR (a i j : Fin N) : divergence4 Q a i j = 0 :=
    constant_trivector_array_zero F hF hgrad _ hRdeg hRhor a i j
  have hd := congrArg (fun T => divergence4 T i j k) hE
  rw [divergence4_eulerWedge3 J hJs hJc hJd,divergence4_mul,hG,hR,mul_zero,add_zero] at hd
  simp only [eulerWedge2,hclosed,mul_zero,sub_zero,add_zero,nsmul_eq_mul] at hd
  have hcoef : (N : CubicPolynomial N) - 3 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show N ≠ 3 by omega)
  exact (mul_eq_zero.mp (show ((N : CubicPolynomial N)-3)*J i j k = 0 by
    linear_combination hd)).resolve_left hcoef

/-- Polynomial Jacobi follows from the explicitly stated geometric Euler
wedge divisibility. Establishing that divisibility from the actual hypersurface
Poisson condition is a separate geometric obligation. -/
theorem contraction_jacobi_of_euler_divisibility (hN : 5 ≤ N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (P : Trivector N)
    (Q : Fin N → Fin N → Fin N → Fin N → CubicPolynomial N)
    (hQs : ∀ a b i j, Q b a i j = -Q a b i j)
    (hQd : ∀ a b i j, (Q a b i j).IsHomogeneous 1)
    (heq : ∀ a b c d,
      eulerWedge3 (jacobiArray (contractionCoefficients F P)) a b c d = F*Q a b c d) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) := by
  apply (JacobiCriterion.satisfiesJacobi_iff_coordinates _ (contraction_skew F P)).mpr
  intro i j k
  change jacobiArray (contractionCoefficients F P) i j k = 0
  exact euler_divisibility_lift_vanishes hN F hF0 hF hgrad _
    (jacobiArray_swap_first _ (contraction_skew F P)) (jacobiArray_cyclic _)
    (contraction_jacobiArray_isHomogeneous F P hF)
    (divergence3_jacobiArray _ (contraction_skew F P) (divergence2_contraction F P))
    (gradientContract3_jacobiArray F _ (contraction_skew F P) (contraction_gradient_zero F P))
    Q hQs hQd heq i j k
end NcCubic.Geometry
