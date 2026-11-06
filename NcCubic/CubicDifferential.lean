module
public import NcCubic.Statement
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.BilinearForm.Basic
/-!
# Cubic differentials and the basepoint-free Hessian system

Paper Lemma 3.1: the Hessian is linear in the evaluation point, symmetric
bilinear in its tangent arguments, and satisfies H_p(w,w) = 2 dF_w(p).
The isolated-gradient-zero hypothesis therefore makes its linear system
basepoint-free. No smoothness comparison or classification is assumed here.
-/

@[expose] public section
noncomputable section
namespace NcCubic.CubicDifferential
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

def differential (F : CubicPolynomial N) (w p : CoordinateSpace N) : ℂ :=
  ∑ i, p i * eval w (pderiv i F)
def hessian (F : CubicPolynomial N) (p v w : CoordinateSpace N) : ℂ :=
  ∑ i, ∑ j, v i * w j * eval p (pderiv i (pderiv j F))

theorem derivative_homogeneous {F : CubicPolynomial N} (hF : F.IsHomogeneous 3) (i : Fin N) :
    (pderiv i F).IsHomogeneous 2 := hF.pderiv

theorem second_derivative_homogeneous {F : CubicPolynomial N}
    (hF : F.IsHomogeneous 3) (i j : Fin N) :
    (pderiv i (pderiv j F)).IsHomogeneous 1 := hF.pderiv.pderiv

theorem euler {F : CubicPolynomial N} (hF : F.IsHomogeneous 3) :
    ∑ i, X i * pderiv i F = 3 • F := hF.sum_X_mul_pderiv

theorem eval_constant {G : CubicPolynomial N} (hG : G.IsHomogeneous 0)
    (p w : CoordinateSpace N) : eval p G = eval w G := by
  have h := (totalDegree_eq_zero_iff_eq_C).mp
    ((totalDegree_zero_iff_isHomogeneous (Fin N)).mpr hG)
  rw [h]
  simp

theorem eval_linear {G : CubicPolynomial N} (hG : G.IsHomogeneous 1)
    (p w : CoordinateSpace N) : eval p G = ∑ i, p i * eval w (pderiv i G) := by
  have h := congrArg (eval p) hG.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, one_smul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_constant hG.pderiv p w]

theorem hessian_gradient {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (p w : CoordinateSpace N) : hessian F p w w = 2 * differential F w p := by
  unfold hessian differential
  simp_rw [eval_linear (second_derivative_homogeneous hF _ _) p w,
    Finset.mul_sum]
  have hquad (i : Fin N) :
      ∑ j, w j * eval w (pderiv j (pderiv i F)) = 2 * eval w (pderiv i F) := by
    have h := congrArg (eval w) (derivative_homogeneous hF i).sum_X_mul_pderiv
    simpa [map_sum, map_mul, nsmul_eq_mul] using h
  have hlin (i j : Fin N) :
      ∑ k, w k * eval w (pderiv k (pderiv j (pderiv i F))) =
        eval w (pderiv j (pderiv i F)) :=
    (eval_linear (second_derivative_homogeneous hF j i) w w).symm
  calc
    _ = ∑ i, ∑ j, ∑ k, p i * (w j * (w k *
        eval w (pderiv k (pderiv j (pderiv i F))))) := by
      conv_lhs =>
        arg 2
        ext i
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [pderiv_comm i j, pderiv_comm i k, pderiv_comm j k]
      ring
    _ = _ := by
      simp_rw [← Finset.mul_sum, hlin, hquad]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem hessian_symm (F : CubicPolynomial N) (p v w : CoordinateSpace N) :
    hessian F p v w = hessian F p w v := by
  unfold hessian
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_comm]
  ring

theorem hessian_add_left (F : CubicPolynomial N) (p v v' w : CoordinateSpace N) :
    hessian F p (v + v') w = hessian F p v w + hessian F p v' w := by
  simp [hessian, add_mul, Finset.sum_add_distrib]

theorem hessian_smul_left (F : CubicPolynomial N) (p v w : CoordinateSpace N) (c : ℂ) :
    hessian F p (c • v) w = c * hessian F p v w := by
  simp [hessian, mul_assoc, Finset.mul_sum]

theorem hessian_add_right (F : CubicPolynomial N) (p v w w' : CoordinateSpace N) :
    hessian F p v (w + w') = hessian F p v w + hessian F p v w' := by
  rw [hessian_symm, hessian_add_left, hessian_symm F p w v, hessian_symm F p w' v]

theorem hessian_smul_right (F : CubicPolynomial N) (p v w : CoordinateSpace N) (c : ℂ) :
    hessian F p v (c • w) = c * hessian F p v w := by
  rw [hessian_symm, hessian_smul_left, hessian_symm F p w v]

def hessianForm (F : CubicPolynomial N) (p : CoordinateSpace N) :
    LinearMap.BilinForm ℂ (CoordinateSpace N) where
  toFun v := {
    toFun := fun w => hessian F p v w
    map_add' := hessian_add_right F p v
    map_smul' := fun c w => hessian_smul_right F p v w c }
  map_add' v v' := by
    apply LinearMap.ext
    intro w
    exact hessian_add_left F p v v' w
  map_smul' c v := by
    apply LinearMap.ext
    intro w
    exact hessian_smul_left F p v w c

theorem hessianForm_symm (F : CubicPolynomial N) (p : CoordinateSpace N) :
    ∀ v w, hessianForm F p v w = hessianForm F p w v := hessian_symm F p

theorem eval_linear_add {G : CubicPolynomial N} (hG : G.IsHomogeneous 1)
    (p q : CoordinateSpace N) : eval (p + q) G = eval p G + eval q G := by
  rw [eval_linear hG (p+q) 0, eval_linear hG p 0, eval_linear hG q 0]
  simp [add_mul, Finset.sum_add_distrib]

theorem eval_linear_smul {G : CubicPolynomial N} (hG : G.IsHomogeneous 1)
    (c : ℂ) (p : CoordinateSpace N) : eval (c • p) G = c * eval p G := by
  rw [eval_linear hG (c • p) 0, eval_linear hG p 0]
  simp [mul_assoc, Finset.mul_sum]

theorem hessian_add_point {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (p q v w : CoordinateSpace N) :
    hessian F (p+q) v w = hessian F p v w + hessian F q v w := by
  unfold hessian
  simp_rw [eval_linear_add (second_derivative_homogeneous hF _ _), mul_add,
    Finset.sum_add_distrib]

theorem hessian_smul_point {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (c : ℂ) (p v w : CoordinateSpace N) :
    hessian F (c • p) v w = c * hessian F p v w := by
  unfold hessian
  simp_rw [eval_linear_smul (second_derivative_homogeneous hF _ _)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The Hessian of a cubic is a linear system of symmetric bilinear forms. -/
def hessianLinearMap (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) :
    CoordinateSpace N →ₗ[ℂ] LinearMap.BilinForm ℂ (CoordinateSpace N) where
  toFun := hessianForm F
  map_add' p q := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact hessian_add_point hF p q v w
  map_smul' c p := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact hessian_smul_point hF c p v w

theorem hessian_basepoint_free {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (w : CoordinateSpace N) (hw : w ≠ 0) :
    ∃ p : CoordinateSpace N, hessian F p w w ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hd (p : CoordinateSpace N) : differential F w p = 0 := by
    have h : 2 * differential F w p = 0 := (hessian_gradient hF p w).symm.trans (hn p)
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  apply hw
  apply hgrad w
  intro i
  have h := hd (Pi.single i 1)
  simpa [differential, Pi.single_apply] using h

theorem hessian_range_basepoint_free {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (w : CoordinateSpace N) (hw : w ≠ 0) :
    ∃ H ∈ LinearMap.range (hessianLinearMap F hF), H w w ≠ 0 := by
  obtain ⟨p, hp⟩ := hessian_basepoint_free hF hgrad w hw
  exact ⟨hessianForm F p, ⟨p, rfl⟩, hp⟩
end NcCubic.CubicDifferential
