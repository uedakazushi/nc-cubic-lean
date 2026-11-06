module
public import NcCubic.HessianCompatibility
public import NcCubic.BlockContraction
public import NcCubic.PolynomialBlocks
import Mathlib.Tactic.FinCases
@[expose] public section
noncomputable section
namespace NcCubic.BlockHessian
open MvPolynomial
open scoped BigOperators
open HessianCompatibility
variable {N k m : ℕ}

def firstIndex (i : Fin 3) : Fin 3 := ![1,2,0] i
def secondIndex (i : Fin 3) : Fin 3 := ![2,0,1] i

theorem contraction_dual_cyclic (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hP : HasBlockTrivector P b) (s : Fin k) (i : Fin 3) :
    contraction P (b.dualBasis (Sum.inl (s, firstIndex i)))
      (b.dualBasis (Sum.inl (s, secondIndex i))) = b (Sum.inl (s,i)) := by
  classical
  funext a
  change P ![b.dualBasis (Sum.inl (s,firstIndex i)),
    b.dualBasis (Sum.inl (s,secondIndex i)), coordinateCovector a] = _
  rw [hP]
  rw [Finset.sum_eq_single s]
  · change Matrix.det (Matrix.of (fun r c : Fin 3 =>
      (![b.dualBasis (Sum.inl (s,firstIndex i)),
        b.dualBasis (Sum.inl (s,secondIndex i)),coordinateCovector a] r)
        (b (Sum.inl (s,c))))) = _
    rw [Matrix.det_fin_three]
    fin_cases i <;>
      simp [firstIndex,secondIndex,
        coordinateCovector]
  · intro t _ hts
    have hst : s ≠ t := Ne.symm hts
    change Matrix.det (Matrix.of (fun r c : Fin 3 =>
      (![b.dualBasis (Sum.inl (s,firstIndex i)),
        b.dualBasis (Sum.inl (s,secondIndex i)),coordinateCovector a] r)
        (b (Sum.inl (t,c))))) = _
    rw [Matrix.det_fin_three]
    fin_cases i <;>
      simp [firstIndex,secondIndex,
        hst,coordinateCovector]
  · simp

theorem contraction_dual_cross (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hP : HasBlockTrivector P b) (s t : Fin k) (hst : s ≠ t) (i j : Fin 3) :
    contraction P (b.dualBasis (Sum.inl (s,i))) (b.dualBasis (Sum.inl (t,j))) = 0 := by
  classical
  funext a
  change P ![b.dualBasis (Sum.inl (s,i)), b.dualBasis (Sum.inl (t,j)),
    coordinateCovector a] = 0
  rw [hP]
  apply Finset.sum_eq_zero
  intro r _
  change Matrix.det (Matrix.of (fun u v : Fin 3 =>
    (![b.dualBasis (Sum.inl (s,i)),b.dualBasis (Sum.inl (t,j)),coordinateCovector a] u)
      (b (Sum.inl (r,v))))) = 0
  rw [Matrix.det_fin_three]
  by_cases hrs : r = s
  · subst r
    simp [Ne.symm hst]
  · simp [Ne.symm hrs]

/-- Compatibility annihilates pairings between different active blocks. -/
theorem compatible_cross_zero (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hP : HasBlockTrivector P b) (H : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hH : Compatible P H) (s t : Fin k) (hst : s ≠ t) (i j : Fin 3) :
    H (b (Sum.inl (s,i))) (b (Sum.inl (t,j))) = 0 := by
  have h := hH ![b.dualBasis (Sum.inl (s,firstIndex i)),
    b.dualBasis (Sum.inl (s,secondIndex i)),
    b.dualBasis (Sum.inl (t,firstIndex j)),
    b.dualBasis (Sum.inl (t,secondIndex j))]
  change H
    (contraction P (b.dualBasis (Sum.inl (s,firstIndex i))) (b.dualBasis (Sum.inl (s,secondIndex i))))
    (contraction P (b.dualBasis (Sum.inl (t,firstIndex j))) (b.dualBasis (Sum.inl (t,secondIndex j)))) +
    H (contraction P (b.dualBasis (Sum.inl (s,secondIndex i))) (b.dualBasis (Sum.inl (t,firstIndex j))))
      (contraction P (b.dualBasis (Sum.inl (s,firstIndex i))) (b.dualBasis (Sum.inl (t,secondIndex j)))) +
    H (contraction P (b.dualBasis (Sum.inl (t,firstIndex j))) (b.dualBasis (Sum.inl (s,firstIndex i))))
      (contraction P (b.dualBasis (Sum.inl (s,secondIndex i))) (b.dualBasis (Sum.inl (t,secondIndex j)))) = 0 at h
  simpa only [contraction_dual_cyclic P b hP,
    contraction_dual_cross P b hP s t hst,
    contraction_dual_cross P b hP t s (Ne.symm hst), map_zero,
    LinearMap.zero_apply, add_zero] using h

theorem eval_directional_second (F : CubicPolynomial N)
    (p v w : CoordinateSpace N) :
    eval p (directionalDerivative v (directionalDerivative w F)) =
      CubicDifferential.hessianForm F p v w := by
  simp [directionalDerivative, CubicDifferential.hessianForm,CubicDifferential.hessian,
    map_sum, map_mul, Finset.mul_sum, mul_assoc]

/-- All compatible Hessians give vanishing mixed partials in a block basis. -/
theorem mixed_derivative_in_basis (F : CubicPolynomial N) (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hP : HasBlockTrivector P b)
    (hH : ∀ p, Compatible P (CubicDifferential.hessianForm F p))
    (s t : Fin k) (hst : s ≠ t) (i j : Fin 3) :
    pderiv (Sum.inl (s,i)) (pderiv (Sum.inl (t,j)) (polynomialInBasis F b)) = 0 := by
  have hz : directionalDerivative (b (Sum.inl (s,i)))
      (directionalDerivative (b (Sum.inl (t,j))) F) = 0 := by
    apply MvPolynomial.funext
    intro p
    rw [eval_directional_second]
    simpa only [map_zero] using compatible_cross_zero P b hP _ (hH p) s t hst i j
  have ht := congrArg (fun G => polynomialInBasis G b) hz
  rw [polynomialInBasis_directionalDerivative, polynomialInBasis_directionalDerivative] at ht
  simpa only [polynomialInBasis, map_zero] using ht

/-- Linear basis substitutions preserve homogeneous degree. -/
theorem homogeneous_in_basis {F : CubicPolynomial N} {n : ℕ} (hF : F.IsHomogeneous n)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) :
    (polynomialInBasis F b).IsHomogeneous n := by
  classical
  unfold polynomialInBasis
  have h := hF.aeval (n := 1) (fun i : Fin N =>
    ∑ j : BlockIndex k m, C ((b j) i) * X j) (fun i => ?_)
  · simpa using h
  · apply IsHomogeneous.sum
    intro j _
    exact (isHomogeneous_X ℂ j).C_mul _

/-- The polynomial-decomposition part of P5, in the original normal-form basis. -/
theorem polynomial_decomposition_in_basis {F : CubicPolynomial N} {n : ℕ}
    (hF : F.IsHomogeneous n) (P : Trivector N) (hk : 1 ≤ k)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hP : HasBlockTrivector P b)
    (hH : ∀ p, Compatible P (CubicDifferential.hessianForm F p)) :
    ∃ f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) ℂ,
      (∀ s, (f s).IsHomogeneous n) ∧
      polynomialInBasis F b = ∑ s, rename (blockVariable s) (f s) := by
  exact PolynomialBlocks.decomposition_of_mixed_derivatives hk _
    (homogeneous_in_basis hF b) (mixed_derivative_in_basis F P b hP hH)

/-- A block tensor and compatible cubic Hessians supply the full normal-form contract. -/
theorem hasBlockNormalForm_of_compatible {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (P : Trivector N) (hk : 1 ≤ k) (hdim : N = 3 * k + m)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hP : HasBlockTrivector P b)
    (hH : ∀ p, Compatible P (CubicDifferential.hessianForm F p)) :
    HasBlockNormalForm F P := by
  obtain ⟨f, hf, heq⟩ := polynomial_decomposition_in_basis hF P hk b hP hH
  exact ⟨k, m, hk, hdim, b, f, hf, hP, heq⟩
end NcCubic.BlockHessian
