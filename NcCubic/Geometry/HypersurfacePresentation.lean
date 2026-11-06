/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Adapted from StacksFrontier.RingTheory.Smooth.PlaneHypersurface at
AxiomMath/Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7.
Upstream Lean code is released under Apache 2.0 license.
-/
module
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
public import StacksFrontier.RingTheory.Smooth.JacobianCriterion
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Actual smoothness criterion for arbitrary affine hypersurfaces

A finite-variable polynomial quotient by one nonzero nonunit equation is
presented by that equation. Its fibre dimension condition is proved, rather
than assumed, from the hypersurface dimension theorem over a field.
-/

@[expose] public noncomputable section
open MvPolynomial
namespace NcCubic.Geometry.HypersurfacePresentation
variable {k σ : Type*} [Field k]

def hypersurfacePresentation (f : MvPolynomial (σ) k) :
    Algebra.Presentation k (MvPolynomial (σ) k ⧸ Ideal.span {f}) (σ) (Fin 1) :=
  (Algebra.Presentation.naive (v := fun _ : Fin 1 => f)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq k (by rw [Set.range_const]))


theorem hypersurfacePresentation_relation (f : MvPolynomial (σ) k) (i : Fin 1) :
    (hypersurfacePresentation f).relation i = f := by
  simp [hypersurfacePresentation, Algebra.Presentation.ofAlgEquiv_relation]


theorem hypersurfacePresentation_algebraMap (f x : MvPolynomial (σ) k) :
    algebraMap (hypersurfacePresentation f).Ring
        (MvPolynomial (σ) k ⧸ Ideal.span {f}) x = Ideal.Quotient.mk _ x := by
  have hval : ∀ i : σ,
      (hypersurfacePresentation f).val i = Ideal.Quotient.mk (Ideal.span {f}) (X i) := by
    intro i
    simp [hypersurfacePresentation, Algebra.Presentation.ofAlgEquiv,
      Algebra.Generators.ofAlgEquiv_val, Algebra.Generators.naive_val]
  rw [Algebra.Generators.algebraMap_apply]
  have h : (MvPolynomial.aeval (hypersurfacePresentation f).val :
        MvPolynomial (σ) k →ₐ[k] _) = Ideal.Quotient.mkₐ k (Ideal.span {f}) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hval]
  exact DFunLike.congr_fun h x


theorem hypersurfacePresentation_jacobian (f : MvPolynomial (σ) k) (e : Fin 1 ↪ σ) :
    (Algebra.PreSubmersivePresentation.mk (hypersurfacePresentation f) e e.injective).jacobian
      = Ideal.Quotient.mk (Ideal.span {f}) (pderiv (e 0) f) := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    show ((Algebra.PreSubmersivePresentation.mk (hypersurfacePresentation f) e
      e.injective).map default) = e 0 from rfl,
    show ((Algebra.PreSubmersivePresentation.mk (hypersurfacePresentation f) e
      e.injective).relation default) = f from hypersurfacePresentation_relation f default]
  exact hypersurfacePresentation_algebraMap f _


theorem hypersurfacePresentation_fiber_dim [Finite σ] (f : MvPolynomial (σ) k) (hf0 : f ≠ 0)
    (hfu : ¬ IsUnit f) (p : Ideal k) [p.IsPrime] :
    Nontrivial (p.Fiber (MvPolynomial (σ) k ⧸ Ideal.span {f})) →
      ringKrullDim (p.Fiber (MvPolynomial (σ) k ⧸ Ideal.span {f}))
        + (Nat.card (Fin 1) : WithBot ℕ∞) = (Nat.card (σ) : WithBot ℕ∞) := by
  intro _
  have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  subst hp
  have ebij : Function.Bijective (algebraMap k ((⊥ : Ideal k).ResidueField)) :=
    ⟨(algebraMap k _).injective, Ideal.algebraMap_residueField_surjective ⊥⟩
  let e : k ≃ₐ[k] (⊥ : Ideal k).ResidueField := AlgEquiv.ofBijective (Algebra.ofId k _) ebij
  let E : (⊥ : Ideal k).Fiber (MvPolynomial (σ) k ⧸ Ideal.span {f}) ≃ₐ[k]
      (MvPolynomial (σ) k ⧸ Ideal.span {f}) :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid k _)
  rw [ringKrullDim_eq_of_ringEquiv E.toRingEquiv]
  simpa using Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton_add_one k σ f hf0 hfu


theorem isSmoothAt_iff_exists_pderiv_notMem [Finite σ] {f : MvPolynomial (σ) k} (hf0 : f ≠ 0)
    (hfu : ¬ IsUnit f) (Q : Ideal (MvPolynomial (σ) k ⧸ Ideal.span {f})) [Q.IsPrime] :
    Algebra.IsSmoothAt k Q ↔
      ∃ i : σ, pderiv i f ∉ Q.comap (Ideal.Quotient.mk (Ideal.span {f})) := by
  rw [Algebra.Presentation.isSmoothAt_iff_exists_jacobian_notMem
    (hypersurfacePresentation f)
    (fun p _ h => hypersurfacePresentation_fiber_dim f hf0 hfu p h) Q]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e 0, by rwa [Ideal.mem_comap, ← hypersurfacePresentation_jacobian f e]⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩, by
      rwa [hypersurfacePresentation_jacobian]⟩

/-- Evaluation at an actual solution factors through the hypersurface coordinate ring. -/
def pointEvaluation (f : MvPolynomial σ k) (x : σ → k) (hx : eval x f = 0) :
    (MvPolynomial σ k ⧸ Ideal.span {f}) →+* k :=
  Ideal.Quotient.lift _ (eval x) (by
    change Ideal.span ({f} : Set (MvPolynomial σ k)) ≤ RingHom.ker (eval x)
    apply Ideal.span_le.mpr
    intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact hx)

@[simp] theorem pointEvaluation_mk (f : MvPolynomial σ k) (x : σ → k)
    (hx : eval x f = 0) (g : MvPolynomial σ k) :
    pointEvaluation f x hx (Ideal.Quotient.mk _ g) = eval x g := by
  simp [pointEvaluation]

instance pointEvaluation_ker_isPrime (f : MvPolynomial σ k) (x : σ → k)
    (hx : eval x f = 0) : (RingHom.ker (pointEvaluation f x hx)).IsPrime :=
  RingHom.ker_isPrime _

/-- A nonzero equation's actual algebraic smoothness at a rational solution is
exactly nonvanishing of one evaluated partial derivative. -/
theorem isSmoothAt_point_iff [Finite σ] {f : MvPolynomial σ k} (hf : f ≠ 0)
    (x : σ → k) (hx : eval x f = 0) :
    Algebra.IsSmoothAt k (RingHom.ker (pointEvaluation f x hx)) ↔
      ∃ i : σ, eval x (pderiv i f) ≠ 0 := by
  have hfu : ¬ IsUnit f := fun hu => (hu.map (eval x)).ne_zero hx
  rw [isSmoothAt_iff_exists_pderiv_notMem hf hfu]
  simp only [Ideal.mem_comap, RingHom.mem_ker, pointEvaluation_mk]
end NcCubic.Geometry.HypersurfacePresentation
