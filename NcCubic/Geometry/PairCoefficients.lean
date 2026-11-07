/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Statement
public import Mathlib.Tactic.Ring
@[expose] public noncomputable section
namespace NcCubic.Geometry
open scoped BigOperators
section Generic
variable {ι κ A : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [CommRing A]
/-- The skew coefficient array of a finite family of ordered coordinate wedges. -/
def pairCoefficients (idx : κ → Fin 2 → ι) (c : κ → A) (i j : ι) : A :=
  ∑ s, ((if i=idx s 0 ∧ j=idx s 1 then c s else 0) -
    (if i=idx s 1 ∧ j=idx s 0 then c s else 0))

omit [Fintype ι] in
theorem pairCoefficients_skew (idx : κ → Fin 2 → ι) (c : κ → A) (i j : ι) :
    pairCoefficients idx c j i = -pairCoefficients idx c i j := by
  unfold pairCoefficients
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [and_comm]
  ring

theorem pairCoefficients_pairing (idx : κ → Fin 2 → ι) (c : κ → A) (y z : ι → A) :
    (∑ i, ∑ j, pairCoefficients idx c i j * y i * z j) =
      ∑ s, c s * (y (idx s 0) * z (idx s 1) - y (idx s 1) * z (idx s 0)) := by
  have hone (a b : ι) (t : A) :
      (∑ i, ∑ j, (if i=a ∧ j=b then t else 0) * y i * z j) = t*y a*z b := by
    simp [ite_and,ite_mul]
  unfold pairCoefficients
  simp only [Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply (Finset.sum_congr rfl fun s _ => ?_)
  simp only [sub_mul,Finset.sum_sub_distrib]
  rw [hone,hone]
  ring
end Generic

/-- Homogeneous coordinate coefficients give a homogeneous skew array. -/
theorem pairCoefficients_homogeneous {N : ℕ} {κ : Type*} [Fintype κ]
    (idx : κ → Fin 2 → Fin N) (c : κ → CubicPolynomial N) (d : ℕ)
    (hc : ∀ s, (c s).IsHomogeneous d) (i j : Fin N) :
    (pairCoefficients idx c i j).IsHomogeneous d := by
  unfold pairCoefficients
  apply MvPolynomial.IsHomogeneous.sum
  intro s _
  apply MvPolynomial.IsHomogeneous.sub
  · split_ifs
    · exact hc s
    · exact MvPolynomial.isHomogeneous_zero (Fin N) ℂ d
  · split_ifs
    · exact hc s
    · exact MvPolynomial.isHomogeneous_zero (Fin N) ℂ d

/-- The usual polynomial bracket of the full skew array is exactly the sum
of its ordered coordinate-wedge brackets, with no extra factor of two. -/
theorem bracketFromPairCoefficients {N : ℕ} {κ : Type*} [Fintype κ]
    (idx : κ → Fin 2 → Fin N) (c : κ → CubicPolynomial N) (f g : CubicPolynomial N) :
    bracketFromCoefficients (pairCoefficients idx c) f g =
      ∑ s, c s * (MvPolynomial.pderiv (idx s 0) f * MvPolynomial.pderiv (idx s 1) g -
        MvPolynomial.pderiv (idx s 1) f * MvPolynomial.pderiv (idx s 0) g) :=
  pairCoefficients_pairing idx c (fun i => MvPolynomial.pderiv i f) (fun i => MvPolynomial.pderiv i g)
end NcCubic.Geometry
