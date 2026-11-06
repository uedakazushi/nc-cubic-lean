/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.ProjectivePoisson
public import NcCubic.Geometry.ProjectiveEquation
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The hypersurface equation ideal is stable under the full degree-zero
bracket, not only under the generating ratio Hamiltonians. -/
theorem projectiveBracket_preserves_equationIdeal
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y : ProjectiveChartRing i)
    (hy : y ∈ Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i))) :
    projectiveBracket F P hF i x y ∈
      Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i)) := by
  let I := Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i))
  let e := Stacks.ProjectiveChart.chartRingEquiv ℂ i
  have hratio (k : Fin n) : projectiveBracket F P hF i (e (X k)) y ∈ I := by
    obtain ⟨z,hz,hval⟩ := projectiveEquationIdeal_stable F P hF i (i.succAbove k) y hy
    have heq : projectiveBracket F P hF i (e (X k)) y = z := by
      apply HomogeneousLocalization.val_injective
      rw [projectiveBracket_val,projectiveChartEquiv_X_val,localizedBracket_chartCoordinate,← hval]
    rw [heq]
    exact hz
  obtain ⟨p,rfl⟩ := e.surjective x
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hz : projectiveBracket F P hF i (e (C c)) y = 0 := by
      apply HomogeneousLocalization.val_injective
      rw [projectiveBracket_val,projectiveChartEquiv_C_val,HomogeneousLocalization.val_zero]
      simp [LocalizedPoisson.bracket]
    rw [hz]
    exact Ideal.zero_mem _
  | add p q hp hq =>
    rw [map_add,projectiveBracket_add_left]
    exact Ideal.add_mem _ hp hq
  | mul_X p k hp =>
    have hm : projectiveBracket F P hF i (e p * e (X k)) y =
        e p * projectiveBracket F P hF i (e (X k)) y +
        e (X k) * projectiveBracket F P hF i (e p) y := by
      apply HomogeneousLocalization.val_injective
      simp only [projectiveBracket_val,HomogeneousLocalization.val_mul,
        HomogeneousLocalization.val_add,LocalizedPoisson.bracket_mul_left _ (contraction_skew F P)]
    rw [map_mul,hm]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hratio k)) (Ideal.mul_mem_left _ _ hp)

/-- The actual coordinate ring of the projective hypersurface chart. -/
abbrev ProjectiveHypersurfaceChartRing (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) :=
  ProjectiveChartRing i ⧸ Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i))

private theorem projectiveBracket_sub_right
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y z : ProjectiveChartRing i) :
    projectiveBracket F P hF i x (y-z) =
      projectiveBracket F P hF i x y - projectiveBracket F P hF i x z := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveBracket_val,HomogeneousLocalization.val_sub]
  simp [LocalizedPoisson.bracket,map_sub,mul_sub,Finset.sum_sub_distrib]
private theorem projectiveBracket_sub_left
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y z : ProjectiveChartRing i) :
    projectiveBracket F P hF i (x-y) z =
      projectiveBracket F P hF i x z - projectiveBracket F P hF i y z := by
  rw [projectiveBracket_skew F P hF i (x-y) z,projectiveBracket_sub_right,
    projectiveBracket_skew F P hF i z x,projectiveBracket_skew F P hF i z y]
  ring

theorem projectiveBracket_quotient_congr
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (a b a' b' : ProjectiveChartRing i)
    (ha : Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) a =
      Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) a')
    (hb : Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) b =
      Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) b') :
    Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) (projectiveBracket F P hF i a b) =
      Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) (projectiveBracket F P hF i a' b') := by
  have hleft : Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) (projectiveBracket F P hF i a b) =
      Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) (projectiveBracket F P hF i a' b) := by
    apply Ideal.Quotient.eq.mpr
    rw [← projectiveBracket_sub_left,projectiveBracket_skew F P hF i (a-a') b]
    exact (Ideal.span {projectiveEquation F hF i}).neg_mem (projectiveBracket_preserves_equationIdeal F P hF i b _ (Ideal.Quotient.eq.mp ha))
  have hright : Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) (projectiveBracket F P hF i a' b) =
      Ideal.Quotient.mk (Ideal.span {projectiveEquation F hF i}) (projectiveBracket F P hF i a' b') := by
    apply Ideal.Quotient.eq.mpr
    rw [← projectiveBracket_sub_right]
    exact projectiveBracket_preserves_equationIdeal F P hF i a' _ (Ideal.Quotient.eq.mp hb)
  exact hleft.trans hright

/-- The Poisson operation on the actual degree-zero hypersurface quotient chart. -/
def projectiveHypersurfaceBracket
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y : ProjectiveHypersurfaceChartRing F hF i) :
    ProjectiveHypersurfaceChartRing F hF i :=
  Quotient.liftOn₂ x y
    (fun a b => Ideal.Quotient.mk _ (projectiveBracket F P hF i a b))
    (fun a b a' b' ha hb => projectiveBracket_quotient_congr F P hF i a b a' b'
      (Quotient.sound ha) (Quotient.sound hb))

@[simp] theorem projectiveHypersurfaceBracket_mk
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (a b : ProjectiveChartRing i) :
    projectiveHypersurfaceBracket F P hF i (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (projectiveBracket F P hF i a b) := rfl

theorem projectiveHypersurfaceBracket_skew
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y : ProjectiveHypersurfaceChartRing F hF i) :
    projectiveHypersurfaceBracket F P hF i x y = -projectiveHypersurfaceBracket F P hF i y x := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
  simp only [projectiveHypersurfaceBracket_mk,projectiveBracket_skew F P hF i a b,map_neg]

theorem projectiveHypersurfaceBracket_add_right
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y z : ProjectiveHypersurfaceChartRing F hF i) :
    projectiveHypersurfaceBracket F P hF i x (y+z) =
      projectiveHypersurfaceBracket F P hF i x y + projectiveHypersurfaceBracket F P hF i x z := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [← map_add,projectiveHypersurfaceBracket_mk,projectiveBracket_add_right]

theorem projectiveHypersurfaceBracket_mul_right
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (x y z : ProjectiveHypersurfaceChartRing F hF i) :
    projectiveHypersurfaceBracket F P hF i x (y*z) =
      y * projectiveHypersurfaceBracket F P hF i x z + z * projectiveHypersurfaceBracket F P hF i x y := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul,projectiveHypersurfaceBracket_mk,projectiveBracket_mul_right]
  simp only [map_add,map_mul,projectiveHypersurfaceBracket_mk]

theorem projectiveHypersurfaceBracket_jacobi
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)))
    (i : Fin (n+1)) (x y z : ProjectiveHypersurfaceChartRing F hF i) :
    projectiveHypersurfaceBracket F P hF i x (projectiveHypersurfaceBracket F P hF i y z) +
    projectiveHypersurfaceBracket F P hF i y (projectiveHypersurfaceBracket F P hF i z x) +
    projectiveHypersurfaceBracket F P hF i z (projectiveHypersurfaceBracket F P hF i x y) = 0 := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c,rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [projectiveHypersurfaceBracket_mk,← map_add]
  rw [projectiveBracket_jacobi F P hF hJac,map_zero]
end NcCubic.Geometry
