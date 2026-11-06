/- Coordinate evaluation for the polynomial exterior Koszul complex. -/
module
public import NcCubic.Geometry.ExteriorKoszul
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.KoszulCoordinates
open scoped BigOperators
variable {R : Type*} [CommRing R] {N r : ℕ}

def coordinateProjection (idx : Fin r → Fin N) : (Fin N → R) →ₗ[R] (Fin r → R) where
  toFun v i := v (idx i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficient (idx : Fin r → Fin N) : (⋀[R]^r (Fin N → R)) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating.compLinearMap (coordinateProjection idx))

theorem coefficient_ιMulti (idx : Fin r → Fin N) (v : Fin r → Fin N → R) :
    coefficient idx (exteriorPower.ιMulti R r v) = Matrix.det (Matrix.of (fun a b => v a (idx b))) := by
  simp only [coefficient, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

def basisVector (i : Fin N) : Fin N → R := Pi.single i 1

theorem coefficient_wedge2 (a b i j : Fin N) :
    coefficient ![i,j] (exteriorPower.ιMulti R 2 ![basisVector a,basisVector b]) =
      basisVector a i * basisVector b j - basisVector a j * basisVector b i := by
  rw [coefficient_ιMulti, Matrix.det_fin_two]
  rfl


theorem coefficient_d2 (f : Fin N → R) (z : ⋀[R]^3 (Fin N → R)) (i j : Fin N) :
    coefficient ![i,j] (Koszul.d (Koszul.seqDual f) 2 z) =
      ∑ a, f a * coefficient ![a,i,j] z := by
  classical
  let rhs : (⋀[R]^3 (Fin N → R)) →ₗ[R] R :=
    ∑ a, f a • coefficient ![a,i,j]
  have hm : (coefficient ![i,j]).comp (Koszul.d (Koszul.seqDual f) 2) = rhs := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      rhs, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [GradedKoszul.koszul_d_ιMulti]
    simp only [map_sum, map_smul, smul_eq_mul, coefficient_ιMulti,
      Matrix.det_fin_two, Matrix.det_fin_three, Matrix.of_apply]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      pow_zero, pow_succ, one_mul, neg_one_mul,
      Fin.zero_succAbove, Fin.succ_succAbove_zero, Fin.succ_succAbove_one,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two]
    simp only [Koszul.seqDual_apply, Finset.sum_mul, Finset.mul_sum]
    simp only [Matrix.vecHead, Matrix.vecTail, neg_neg, add_zero]
    simp only [neg_mul, Finset.sum_mul]
    simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    ring
  have hz := congrArg (fun L : (⋀[R]^3 (Fin N → R)) →ₗ[R] R => L z) hm
  simpa only [LinearMap.comp_apply, rhs, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul] using hz
end NcCubic.Geometry.KoszulCoordinates
