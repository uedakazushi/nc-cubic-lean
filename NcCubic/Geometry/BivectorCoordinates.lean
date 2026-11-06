/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local coordinate/exterior comparison; upstream licenses are preserved.
-/
module
public import NcCubic.Geometry.KoszulCoordinates
public import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.BivectorCoordinates
open MvPolynomial
open KoszulCoordinates
open scoped BigOperators

abbrev Poly (N : ℕ) := MvPolynomial (Fin N) ℂ

def bivector {N : ℕ} (q : Fin N → Fin N → Poly N) :
    ⋀[Poly N]^2 (Fin N → Poly N) :=
  ∑ a, ∑ b, (C (1 / 2 : ℂ) * q a b) • exteriorPower.ιMulti (Poly N) 2
    ![basisVector a,basisVector b]

theorem coefficient_bivector {N : ℕ} (q : Fin N → Fin N → Poly N)
    (hskew : ∀ i j, q j i = -q i j) (i j : Fin N) :
    coefficient ![i,j] (bivector q) = q i j := by
  classical
  simp only [bivector, map_sum, map_smul, smul_eq_mul]
  simp_rw [coefficient_wedge2]
  simp only [basisVector, Pi.single_apply]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite,
    mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hskew i j]
  have hc : (C (1 / 2 : ℂ) : Poly N) + C (1 / 2 : ℂ) = 1 := by
    rw [← map_add]
    norm_num
  linear_combination q i j * hc

/-- Exterior basis coordinates are the determinant coefficient evaluator on
the corresponding increasing list of indices. -/
theorem basis_repr_eq_coefficient {R : Type*} [CommRing R] {N n : ℕ}
    (s : Set.powersetCard (Fin N) n) (z : ⋀[R]^n (Fin N → R)) :
    ((Pi.basisFun R (Fin N)).exteriorPower n).repr z s =
      coefficient (Set.powersetCard.ofFinEmbEquiv.symm s) z := by
  have hm : ((Pi.basisFun R (Fin N)).exteriorPower n).coord s =
      coefficient (Set.powersetCard.ofFinEmbEquiv.symm s) := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply]
    rw [Module.Basis.coord_apply, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, coefficient_ιMulti]
    congr 1
  exact DFunLike.congr_fun hm z

theorem bivector_homogeneous {N : ℕ} (q : Fin N → Fin N → Poly N)
    (hskew : ∀ i j, q j i = -q i j)
    (hdegree : ∀ i j, (q i j).IsHomogeneous 2)
    (s : Set.powersetCard (Fin N) 2) :
    (((Pi.basisFun (Poly N) (Fin N)).exteriorPower 2).repr (bivector q) s).IsHomogeneous 2 := by
  rw [basis_repr_eq_coefficient]
  let idx := Set.powersetCard.ofFinEmbEquiv.symm s
  have he : (idx : Fin 2 → Fin N) = ![idx 0,idx 1] := by
    funext i; fin_cases i <;> rfl
  rw [show Set.powersetCard.ofFinEmbEquiv.symm s = ![idx 0,idx 1] from he]
  rw [coefficient_bivector q hskew]
  exact hdegree _ _

end NcCubic.Geometry.BivectorCoordinates

namespace NcCubic.Geometry.BivectorCoordinates
open MvPolynomial
open KoszulCoordinates
open scoped BigOperators

theorem coefficient_d1 {R : Type*} [CommRing R] {N : ℕ}
    (g : Fin N → R) (z : ⋀[R]^2 (Fin N → R)) (j : Fin N) :
    coefficient ![j] (Koszul.d (Koszul.seqDual g) 1 z) =
      ∑ i, g i * coefficient ![i,j] z := by
  have hm : (coefficient ![j]).comp (Koszul.d (Koszul.seqDual g) 1) =
      ∑ i, g i • coefficient ![i,j] := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply]
    rw [GradedKoszul.koszul_d_ιMulti]
    simp only [map_sum, map_smul, smul_eq_mul, coefficient_ιMulti,
      Matrix.det_fin_one, Matrix.of_apply]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      coefficient_ιMulti, Matrix.det_fin_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Koszul.seqDual_apply,
      Function.comp_apply]
    simp only [Finset.mul_sum, Finset.sum_mul]
    change (∑ x : Fin 2, ∑ i, (-1 : R)^x.val * (v x i * g i) * v (x.succAbove 0) j) = _
    rw [Fin.sum_univ_two]
    norm_num only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_mul, neg_one_mul,
      show (0 : Fin 2).succAbove (0 : Fin 1) = 1 from rfl,
      show (1 : Fin 2).succAbove (0 : Fin 1) = 0 from rfl]
    simp only [neg_mul, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
    simp only [← sub_eq_add_neg]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    using DFunLike.congr_fun hm z

end NcCubic.Geometry.BivectorCoordinates

namespace NcCubic.Geometry.BivectorCoordinates
open MvPolynomial
open KoszulCoordinates
open scoped BigOperators

/-- The exterior Koszul cycle condition is exactly the coordinate Casimir
condition, with no normalization or sign discrepancy. -/
theorem bivector_cycle_iff {N : ℕ} (q : Fin N → Fin N → Poly N)
    (hskew : ∀ i j, q j i = -q i j) (g : Fin N → Poly N) :
    Koszul.d (Koszul.seqDual g) 1 (bivector q) = 0 ↔
      ∀ j, ∑ i, q i j * g i = 0 := by
  constructor
  · intro hz j
    have h := congrArg (coefficient ![j]) hz
    rw [coefficient_d1] at h
    simp only [coefficient_bivector q hskew, map_zero] at h
    simpa only [mul_comm] using h
  · intro hz
    apply ((Pi.basisFun (Poly N) (Fin N)).exteriorPower 1).ext_elem
    intro s
    simp only [map_zero, Finsupp.zero_apply]
    rw [basis_repr_eq_coefficient]
    let idx := Set.powersetCard.ofFinEmbEquiv.symm s
    have he : (idx : Fin 1 → Fin N) = ![idx 0] := by
      funext k; fin_cases k; rfl
    rw [show Set.powersetCard.ofFinEmbEquiv.symm s = ![idx 0] from he]
    rw [coefficient_d1]
    simp only [coefficient_bivector q hskew]
    simpa only [mul_comm] using hz (idx 0)

end NcCubic.Geometry.BivectorCoordinates
