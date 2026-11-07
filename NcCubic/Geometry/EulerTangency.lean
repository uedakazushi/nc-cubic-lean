/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
The geometric coefficient divisibility remains an explicit hypothesis. -/
module
public import NcCubic.Geometry.HomogeneousDivision
public import NcCubic.Geometry.TangentRepresentative
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

theorem radial_of_euler_wedge_zero (w : Fin N → CubicPolynomial N)
    (hd : ∀ i, (w i).IsHomogeneous 4)
    (hz : ∀ i j, eulerWedge1 w i j = 0) :
    ∃ h : CubicPolynomial N, ∀ j, w j = h * X j := by
  let D := ∑ a, pderiv a (w a)
  have he (j : Fin N) : divergence2 (eulerWedge1 w) j =
      (N+3 : CubicPolynomial N)*w j - X j*D := by
    simp only [divergence2,eulerWedge1,map_sub,pderiv_mul,
      Finset.sum_sub_distrib,Finset.sum_add_distrib]
    have h1 : (∑ a : Fin N, pderiv a (X a) * w j) = N • w j := by simp
    have h2 : (∑ a : Fin N, X a * pderiv a (w j)) = 4 • w j :=
      (hd j).sum_X_mul_pderiv
    have h3 : (∑ a : Fin N, pderiv a (X j)*w a) = w j := by
      simp [pderiv_X,Pi.single_apply]
    rw [h1,h2,h3]
    simp only [D,Finset.mul_sum,nsmul_eq_mul]
    ring
  let c : CubicPolynomial N := C (((N:ℂ)+3)⁻¹)
  have hc : c*(N+3 : CubicPolynomial N)=1 := by
    have hcn : C ((N:ℂ)+3)=(N+3:CubicPolynomial N) := by simp only [map_add,map_natCast,map_ofNat]
    rw [←hcn]
    change C (((N:ℂ)+3)⁻¹)*C ((N:ℂ)+3)=1
    rw [← map_mul,inv_mul_cancel₀ (by exact_mod_cast (show N+3≠0 by omega)),map_one]
  refine ⟨c*D,fun j => ?_⟩
  have hh := he j
  simp only [divergence2,hz,map_zero,Finset.sum_const_zero] at hh
  have hh' := congrArg (fun z => c*z) hh
  calc
    w j = c*((N+3 : CubicPolynomial N)*w j) := by rw [← mul_assoc,hc,one_mul]
    _ = c*(X j*D) := by linear_combination -hh'
    _ = (c*D)*X j := by ring

/-- Euler-wedge divisibility produces a linear vector field and a radial error. -/
theorem exists_linear_tangency_of_euler_divisibility (hN : 0 < N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (v : Fin N → CubicPolynomial N) (hv : ∀ i, (v i).IsHomogeneous 4)
    (hdiv : ∀ i j, F ∣ eulerWedge1 v i j) :
    ∃ A : Fin N → CubicPolynomial N, (∀ i, (A i).IsHomogeneous 1) ∧
      ∃ h : CubicPolynomial N, ∀ j, v j = F*A j+h*X j := by
  classical
  choose Q hQ using hdiv
  let R := fun i j => homogeneousComponent 2 (Q i j)
  have hR (i j : Fin N) : eulerWedge1 v i j = F*R i j := by
    have hd : (eulerWedge1 v i j).IsHomogeneous 5 :=
      ((isHomogeneous_X ℂ i).mul (hv j)).sub ((isHomogeneous_X ℂ j).mul (hv i))
    have hh := congrArg (homogeneousComponent 5) (hQ i j)
    rw [homogeneousComponent_eq_self hd] at hh
    exact hh.trans (homogeneousComponent_mul_homogeneous_left (b:=2) _ hF)
  have hRs (i j : Fin N) : R j i = -R i j := by
    apply mul_left_cancel₀ hF0
    rw [← hR j i]
    calc
      _ = -eulerWedge1 v i j := by unfold eulerWedge1; ring
      _ = F*(-R i j) := by rw [hR]; ring
  have hRd (i j : Fin N) : (R i j).IsHomogeneous 2 := homogeneousComponent_isHomogeneous _ _
  have hclosed (i j k : Fin N) : eulerWedge2 R i j k = 0 := by
    apply (mul_eq_zero.mp (show F*eulerWedge2 R i j k=0 by
      calc
        _ = X i*(F*R j k)-X j*(F*R i k)+X k*(F*R i j) := by unfold eulerWedge2; ring
        _ = 0 := by rw [←hR,←hR,←hR]; unfold eulerWedge1; ring)).resolve_left hF0
  have hdelta (i j : Fin N) : (N:CubicPolynomial N)*R i j =
      eulerWedge1 (divergence2 R) i j := by
    have hh := divergence3_eulerWedge2 R hRs hRd i j
    simp only [divergence3,hclosed,map_zero,Finset.sum_const_zero,nsmul_eq_mul] at hh
    linear_combination -hh
  let c : CubicPolynomial N := C ((N:ℂ)⁻¹)
  have hc : c*(N:CubicPolynomial N)=1 := by
    change C ((N:ℂ)⁻¹)*C (N:ℂ)=1
    rw [←map_mul,inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_zero_of_lt hN)),map_one]
  let A := fun i => c*divergence2 R i
  have hA (i : Fin N) : (A i).IsHomogeneous 1 := by
    apply IsHomogeneous.C_mul
    apply IsHomogeneous.sum
    intro a _
    simpa using (hRd a i).pderiv (i:=a)
  have hEA (i j : Fin N) : eulerWedge1 A i j = R i j := by
    calc
      _ = c*eulerWedge1 (divergence2 R) i j := by unfold eulerWedge1 A; ring
      _ = c*((N:CubicPolynomial N)*R i j) := by rw [hdelta]
      _ = R i j := by rw [←mul_assoc,hc,one_mul]
  let w := fun i => v i-F*A i
  have hw (i : Fin N) : (w i).IsHomogeneous 4 := (hv i).sub (hF.mul (hA i))
  have hwz (i j : Fin N) : eulerWedge1 w i j=0 := by
    calc
      _ = eulerWedge1 v i j-F*eulerWedge1 A i j := by unfold eulerWedge1 w; ring
      _ = 0 := by rw [hEA,hR,sub_self]
  obtain ⟨h,hh⟩ := radial_of_euler_wedge_zero w hw hwz
  refine ⟨A,hA,h,fun j => ?_⟩
  have hj := hh j
  change v j-F*A j=h*X j at hj
  linear_combination hj

/-- Tangency divisibility of an actual skew quadratic bivector yields the
precise linear correction formula, without a geometric tangency oracle. -/
theorem tangency_formula_of_euler_coefficients_divisible (hN : 0 < N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (q : Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ i j, q j i = -q i j) (hd : ∀ i j, (q i j).IsHomogeneous 2)
    (hdiv : ∀ i j, F ∣ eulerWedge1 (gradientContract2 F q) i j) :
    ∃ A : Fin N → CubicPolynomial N, (∀ i, (A i).IsHomogeneous 1) ∧
      ∀ j, gradientContract2 F q j =
        F*A j-C (1/3:ℂ)*vectorDerivative F A*X j := by
  have hv (j : Fin N) : (gradientContract2 F q j).IsHomogeneous 4 := by
    apply IsHomogeneous.sum
    intro i _
    exact (hd i j).mul (hF.pderiv (i:=i))
  obtain ⟨A,hA,h,ht⟩ := exists_linear_tangency_of_euler_divisibility hN F hF0 hF _ hv hdiv
  have hr := tangent_scalar_relation F hF hF0 q hs A h ht
  have hc : (C (1/3:ℂ):CubicPolynomial N)*3=1 := by
    rw [show (3:CubicPolynomial N)=C (3:ℂ) by simp only [map_ofNat],←map_mul]
    norm_num
  have hh : h = -C (1/3:ℂ)*vectorDerivative F A := by
    calc
      h = (C (1/3:ℂ)*3)*h := by rw [hc,one_mul]
      _ = -C (1/3:ℂ)*vectorDerivative F A := by linear_combination C (1/3:ℂ)*hr
  refine ⟨A,hA,fun j => ?_⟩
  rw [ht,hh]
  ring

/-- Coefficientwise tangency divisibility supplies a genuine horizontal
quadratic representative by the explicit Euler correction. -/
theorem horizontal_of_euler_coefficients_divisible (hN : 0 < N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (q : Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ i j, q j i = -q i j) (hd : ∀ i j, (q i j).IsHomogeneous 2)
    (hdiv : ∀ i j, F ∣ eulerWedge1 (gradientContract2 F q) i j) :
    ∃ A : Fin N → CubicPolynomial N, (∀ i, (A i).IsHomogeneous 1) ∧
      (∀ j, gradientContract2 F
        (fun i j => q i j-(1/3:ℂ) • eulerWedge1 A i j) j=0) ∧
      (∀ i j, (q i j-(1/3:ℂ) • eulerWedge1 A i j).IsHomogeneous 2) ∧
      ∀ i j, q j i-(1/3:ℂ) • eulerWedge1 A j i =
        -(q i j-(1/3:ℂ) • eulerWedge1 A i j) := by
  obtain ⟨A,hA,h,ht⟩ := exists_linear_tangency_of_euler_divisibility hN F hF0 hF _
    (fun j => by
      apply IsHomogeneous.sum
      intro i _
      exact (hd i j).mul (hF.pderiv (i:=i))) hdiv
  exact ⟨A,hA,corrected_tangent_representative F hF hF0 q hs A h ht,
    corrected_tangent_homogeneous q hd A hA,corrected_tangent_skew q hs A⟩

end NcCubic.Geometry
