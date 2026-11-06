/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Statement
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic
open MvPolynomial
open scoped BigOperators
/-- Formal polynomial chain rule for arbitrary polynomial substitution. -/
theorem pderiv_aeval {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (x : ι → MvPolynomial κ ℂ) (f : MvPolynomial ι ℂ) (j : κ) :
    pderiv j (aeval x f) = ∑ i, aeval x (pderiv i f) * pderiv j (x i) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f a hf =>
    simp only [map_mul, aeval_X, pderiv_mul, hf, map_add,
      Finset.sum_add_distrib, add_mul, Finset.sum_mul]
    simp only [pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero,
      mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Formal chain rule in the precise basis substitution used by the target. -/
theorem pderiv_polynomialInBasis {N k m : ℕ} (F : CubicPolynomial N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (j : BlockIndex k m) :
    pderiv j (polynomialInBasis F b) =
      ∑ i : Fin N, C ((b j) i) * polynomialInBasis (pderiv i F) b := by
  classical
  unfold polynomialInBasis
  rw [pderiv_aeval]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [map_sum, pderiv_C_mul, pderiv_X, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- The two coefficient matrices for a basis and its coordinate map are inverses. -/
theorem basis_matrix_inverse_left {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (i l : Fin N) :
    ∑ j : BlockIndex k m, (b j) i * b.repr (Pi.single l 1) j =
      (Pi.single l (1 : ℂ) : CoordinateSpace N) i := by
  classical
  have h := congrArg (fun v : CoordinateSpace N => v i) (b.sum_repr (Pi.single l 1))
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h

theorem basis_matrix_inverse_right {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (j l : BlockIndex k m) :
    ∑ i : Fin N, b.repr (Pi.single i 1) j * (b l) i = if j = l then 1 else 0 := by
  classical
  have h := congrArg (fun v : CoordinateSpace N => b.repr v j) (pi_eq_sum_univ' (b l))
  simpa only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply, mul_comm, eq_comm] using h.symm

/-- The inverse basis substitution, given by the dual coordinate matrix. -/
def polynomialFromBasis {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) :
    MvPolynomial (BlockIndex k m) ℂ →ₐ[ℂ] CubicPolynomial N :=
  aeval (fun j => ∑ i : Fin N, C (b.repr (Pi.single i 1) j) * X i)

theorem polynomialFromBasis_basis_X {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (i : Fin N) :
    polynomialFromBasis b (∑ j : BlockIndex k m, C ((b j) i) * X j) = X i := by
  classical
  simp only [polynomialFromBasis, map_sum, map_mul, aeval_C, aeval_X]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ l : Fin N, C (∑ j : BlockIndex k m, (b j) i * b.repr (Pi.single l 1) j) * X l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_mul]
      simp only [MvPolynomial.algebraMap_eq]
      ring
    _ = X i := by
      simp only [basis_matrix_inverse_left]
      simp [Pi.single_apply]

theorem polynomialInBasis_inverse_X {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (j : BlockIndex k m) :
    polynomialInBasis (∑ i : Fin N, C (b.repr (Pi.single i 1) j) * X i) b = X j := by
  classical
  simp only [polynomialInBasis, map_sum, map_mul, aeval_C, aeval_X]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ l : BlockIndex k m, C (∑ i : Fin N, b.repr (Pi.single i 1) j * (b l) i) * X l := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul]
      simp only [MvPolynomial.algebraMap_eq]
      ring
    _ = X j := by
      simp only [basis_matrix_inverse_right]
      simp

/-- An arbitrary basis induces an algebra isomorphism, not merely a substitution map. -/
def polynomialBasisEquiv {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) :
    CubicPolynomial N ≃ₐ[ℂ] MvPolynomial (BlockIndex k m) ℂ := by
  classical
  refine AlgEquiv.ofAlgHom
    (aeval (fun i : Fin N => ∑ j : BlockIndex k m, C ((b j) i) * X j))
    (polynomialFromBasis b) ?_ ?_
  · apply MvPolynomial.algHom_ext
    intro j
    change polynomialInBasis (polynomialFromBasis b (X j)) b = X j
    simpa only [polynomialFromBasis, aeval_X] using polynomialInBasis_inverse_X b j
  · apply MvPolynomial.algHom_ext
    intro i
    change polynomialFromBasis b ((aeval (fun i : Fin N =>
      ∑ j : BlockIndex k m, C ((b j) i) * X j)) (X i)) = X i
    simpa only [aeval_X] using polynomialFromBasis_basis_X b i

theorem polynomialBasisEquiv_apply {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (F : CubicPolynomial N) :
    polynomialBasisEquiv b F = polynomialInBasis F b := rfl
end NcCubic
