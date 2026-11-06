/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.AffineChart
public import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.AffineChart
open MvPolynomial
open scoped BigOperators
variable {K σ : Type*} [Field K] [Infinite K] [Fintype σ]

omit [Infinite K] in
/-- Evaluation of a homogeneous polynomial respects scalar dilation. -/
theorem eval_scale_of_homogeneous {τ : Type*} [Fintype τ]
    {F : MvPolynomial τ K} {d : ℕ} (hF : F.IsHomogeneous d)
    (t : K) (x : τ → K) : eval (fun i => t * x i) F = t^d * eval x F := by
  classical
  induction hF using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial a r ha =>
    have hs : ∑ i, a i = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using ha
    simp only [eval_monomial]
    rw [Finsupp.prod_fintype _ _ (by intro i; simp),
      Finsupp.prod_fintype _ _ (by intro i; simp)]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs]
    ring

/-- Dehomogenization is injective on each homogeneous degree over an
infinite field, so a nonzero homogeneous equation stays nonzero on a chart. -/
theorem dehomogenize_ne_zero {F : MvPolynomial (σ ⊕ Unit) K} {d : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) : dehomogenize F ≠ 0 := by
  classical
  intro hz
  apply hF0
  apply MvPolynomial.funext_set (fun _ => ({0} : Set K)ᶜ)
    (fun _ => (Set.finite_singleton (0 : K)).infinite_compl)
  intro x hx
  have ht : x (Sum.inr ()) ≠ 0 := by
    exact hx (Sum.inr ()) (Set.mem_univ _) 
  let y : σ → K := fun i => (x (Sum.inr ()))⁻¹ * x (Sum.inl i)
  have he : eval (lift y) F = 0 := by
    rw [← eval_dehomogenize, hz, map_zero]
  have heq : (fun i => x (Sum.inr ()) * lift y i) = x := by
    funext i
    cases i with
    | inl i => simp [lift,y, ht]
    | inr u => cases u; simp [lift]
  have hs := eval_scale_of_homogeneous hF (x (Sum.inr ())) (lift y)
  rw [heq,he,mul_zero] at hs
  simpa using hs
end NcCubic.Geometry.AffineChart
