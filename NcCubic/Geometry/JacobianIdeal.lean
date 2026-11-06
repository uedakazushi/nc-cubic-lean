/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.AffineChart
public import Mathlib.RingTheory.Nullstellensatz
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
variable {K σ : Type*} [Field K]

/-- The equation together with all affine Jacobian entries. -/
def equationJacobianIdeal (f : MvPolynomial σ K) : Ideal (MvPolynomial σ K) :=
  Ideal.span ({f} ∪ Set.range (fun i => pderiv i f))

/-- The affine derivative ideal in the actual hypersurface quotient ring. -/
def quotientJacobianIdeal (f : MvPolynomial σ K) :
    Ideal (MvPolynomial σ K ⧸ Ideal.span ({f} : Set (MvPolynomial σ K))) :=
  Ideal.span (Set.range (fun i => Ideal.Quotient.mk (Ideal.span ({f} : Set _)) (pderiv i f)))

/-- Nullstellensatz upgrades the rational Jacobian test to a unit ideal. -/
theorem equationJacobianIdeal_eq_top [Finite σ] [IsAlgClosed K]
    (f : MvPolynomial σ K)
    (hsmooth : ∀ x : σ → K, eval x f = 0 → ∃ i, eval x (pderiv i f) ≠ 0) :
    equationJacobianIdeal f = ⊤ := by
  have hz : zeroLocus K (equationJacobianIdeal f) = ∅ := by
    rw [equationJacobianIdeal, zeroLocus_span]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hf : eval x f = 0 := hx f (Set.mem_union_left _ (Set.mem_singleton f))
    obtain ⟨i,hi⟩ := hsmooth x hf
    exact hi (hx (pderiv i f) (Set.mem_union_right _ (Set.mem_range_self i)))
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hz, vanishingIdeal_empty]

/-- The Jacobian ideal in the quotient is the image of equation and derivatives. -/
theorem quotientJacobianIdeal_eq_map (f : MvPolynomial σ K) :
    quotientJacobianIdeal f = Ideal.map (Ideal.Quotient.mk (Ideal.span ({f} : Set _)))
      (equationJacobianIdeal f) := by
  classical
  rw [equationJacobianIdeal, Ideal.map_span, Set.image_union, Set.image_singleton]
  have hf : Ideal.Quotient.mk (Ideal.span ({f} : Set _)) f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton f))
  rw [hf]
  have hi : (Ideal.Quotient.mk (Ideal.span ({f} : Set _))) ''
      Set.range (fun i => pderiv i f) =
      Set.range (fun i => Ideal.Quotient.mk (Ideal.span ({f} : Set _)) (pderiv i f)) := by
    ext x
    constructor
    · rintro ⟨y,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨pderiv i f,⟨i,rfl⟩,rfl⟩
  rw [hi, Set.singleton_union, Ideal.span_insert_zero]
  rfl

/-- The derivatives generate the unit ideal in the genuine hypersurface ring. -/
theorem quotientJacobianIdeal_eq_top [Finite σ] [IsAlgClosed K]
    (f : MvPolynomial σ K)
    (hsmooth : ∀ x : σ → K, eval x f = 0 → ∃ i, eval x (pderiv i f) ≠ 0) :
    quotientJacobianIdeal f = ⊤ := by
  rw [quotientJacobianIdeal_eq_map, equationJacobianIdeal_eq_top f hsmooth, Ideal.map_top]

/-- Every prime of the hypersurface ring belongs to a derivative principal
open; hence these opens cover the whole affine spectrum, including nonclosed points. -/
theorem exists_derivative_notMem_prime [Finite σ] [IsAlgClosed K]
    (f : MvPolynomial σ K)
    (hsmooth : ∀ x : σ → K, eval x f = 0 → ∃ i, eval x (pderiv i f) ≠ 0)
    (p : Ideal (MvPolynomial σ K ⧸ Ideal.span ({f} : Set (MvPolynomial σ K))))
    [hp : p.IsPrime] :
    ∃ i, Ideal.Quotient.mk (Ideal.span ({f} : Set _)) (pderiv i f) ∉ p := by
  by_contra! hall
  have hle : quotientJacobianIdeal f ≤ p := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hall i
  rw [quotientJacobianIdeal_eq_top f hsmooth] at hle
  exact hp.ne_top (top_le_iff.mp hle)
end NcCubic.Geometry

namespace NcCubic.Geometry.AffineChart
open MvPolynomial
variable {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]

/-- Isolated homogeneous gradient zero implies the global Jacobian unit
ideal on every standard affine hypersurface chart. -/
theorem dehomogenized_quotientJacobianIdeal_eq_top
    (F : MvPolynomial (σ ⊕ Unit) K) {d : ℕ} (hF : F.IsHomogeneous d)
    (hgrad : ∀ x : σ ⊕ Unit → K, (∀ i, eval x (pderiv i F) = 0) → x = 0) :
    quotientJacobianIdeal (dehomogenize F) = ⊤ := by
  apply quotientJacobianIdeal_eq_top
  intro x hx
  apply (exists_nonzero_derivative_iff F hF x hx).mpr
  by_contra! hall
  exact lift_ne_zero x (hgrad (lift x) hall)
end NcCubic.Geometry.AffineChart
