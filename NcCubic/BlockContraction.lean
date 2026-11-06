module
public import NcCubic.JacobianBlocks
public import NcCubic.PolynomialCoordinates
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic
open MvPolynomial
open scoped BigOperators

def directionalDerivative {N : ℕ} (v : CoordinateSpace N) (F : CubicPolynomial N) :
    CubicPolynomial N := ∑ i, C (v i) * pderiv i F

/-- A Jacobian bracket expressed in three constant vector directions. -/
def directionalJacobian {N : ℕ} (v : Fin 3 → CoordinateSpace N)
    (F f g : CubicPolynomial N) : CubicPolynomial N :=
  (directionalDerivative (v 0) f * directionalDerivative (v 1) g -
    directionalDerivative (v 1) f * directionalDerivative (v 0) g) * directionalDerivative (v 2) F +
  (directionalDerivative (v 1) f * directionalDerivative (v 2) g -
    directionalDerivative (v 2) f * directionalDerivative (v 1) g) * directionalDerivative (v 0) F +
  (directionalDerivative (v 2) f * directionalDerivative (v 0) g -
    directionalDerivative (v 0) f * directionalDerivative (v 2) g) * directionalDerivative (v 1) F

/-- Determinant expansion of one volume tensor's contraction bracket. -/
theorem determinant_contraction {N : ℕ} (v : Fin 3 → CoordinateSpace N)
    (F f g : CubicPolynomial N) :
    (∑ i, ∑ j, ∑ a,
      C (Matrix.det (Matrix.of (fun r c : Fin 3 => (![coordinateCovector i, coordinateCovector j,
        coordinateCovector a] r) (v c)))) * pderiv i f * pderiv j g * pderiv a F) =
      directionalJacobian v F f g := by
  have hd (i j a : Fin N) :
      Matrix.det (Matrix.of (fun r c : Fin 3 =>
        (![coordinateCovector i, coordinateCovector j, coordinateCovector a] r) (v c))) =
      v 0 i * v 1 j * v 2 a - v 0 i * v 2 j * v 1 a -
      v 1 i * v 0 j * v 2 a + v 1 i * v 2 j * v 0 a +
      v 2 i * v 0 j * v 1 a - v 2 i * v 1 j * v 0 a := by
    rw [Matrix.det_fin_three]
    rfl
  simp only [hd, map_add, map_sub, map_mul]
  unfold directionalJacobian directionalDerivative
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [mul_assoc]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The normal-form tensor makes the contraction bracket a sum of
three-direction Jacobian brackets before changing coordinates. -/
theorem contraction_eq_directionalBlocks {N k m : ℕ} (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hP : HasBlockTrivector P b) (F f g : CubicPolynomial N) :
    bracketFromCoefficients (contractionCoefficients F P) f g =
      ∑ s : Fin k, directionalJacobian (fun r => b (Sum.inl (s, r))) F f g := by
  classical
  have hc (i j a : Fin N) : trivectorCoefficient P i j a =
      ∑ s : Fin k, Matrix.det (Matrix.of (fun r c : Fin 3 =>
        (![coordinateCovector i, coordinateCovector j, coordinateCovector a] r)
          (b (Sum.inl (s, c))))) := hP _
  have commute (T : Fin N → Fin N → Fin N → Fin k → CubicPolynomial N) :
      (∑ i, ∑ j, ∑ a, ∑ s, T i j a s) = ∑ s, ∑ i, ∑ j, ∑ a, T i j a s := by
    calc
      _ = ∑ i, ∑ j, ∑ s, ∑ a, T i j a s := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ s, ∑ j, ∑ a, T i j a s := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by rw [Finset.sum_comm]
  simp only [bracketFromCoefficients, contractionCoefficients, hc, map_sum, Finset.sum_mul]
  rw [commute]
  apply Finset.sum_congr rfl
  intro s _
  rw [← determinant_contraction]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Basis substitution sends a derivative in a basis vector to the
corresponding coordinate partial derivative. -/
theorem polynomialInBasis_directionalDerivative {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (j : BlockIndex k m) (F : CubicPolynomial N) :
    polynomialInBasis (directionalDerivative (b j) F) b =
      pderiv j (polynomialInBasis F b) := by
  classical
  rw [pderiv_polynomialInBasis]
  simp only [directionalDerivative, polynomialInBasis, map_sum, map_mul, aeval_C, MvPolynomial.algebraMap_eq]

/-- The directional Jacobian becomes an ordinary coordinate Jacobian. -/
theorem polynomialInBasis_directionalJacobian {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (s : Fin k)
    (F f g : CubicPolynomial N) :
    polynomialInBasis (directionalJacobian (fun r => b (Sum.inl (s,r))) F f g) b =
      Jacobian.bracket (Sum.inl (s,0)) (Sum.inl (s,1)) (Sum.inl (s,2))
        (polynomialInBasis F b) (polynomialInBasis f b) (polynomialInBasis g b) := by
  simp only [directionalJacobian, polynomialInBasis, map_add, map_sub, map_mul]
  change (polynomialInBasis (directionalDerivative (b (Sum.inl (s,0))) f) b *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,1))) g) b -
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,1))) f) b *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,0))) g) b) *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,2))) F) b +
    (polynomialInBasis (directionalDerivative (b (Sum.inl (s,1))) f) b *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,2))) g) b -
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,2))) f) b *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,1))) g) b) *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,0))) F) b +
    (polynomialInBasis (directionalDerivative (b (Sum.inl (s,2))) f) b *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,0))) g) b -
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,0))) f) b *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,2))) g) b) *
    polynomialInBasis (directionalDerivative (b (Sum.inl (s,1))) F) b = _
  simp_rw [polynomialInBasis_directionalDerivative]
  simp only [Jacobian.bracket, polynomialInBasis]
  ring

/-- Differentiation in an active block sees exactly its own potential. -/
theorem pderiv_block_sum {k m : ℕ}
    (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) ℂ) (s : Fin k) (r : Fin 3) :
    pderiv (Sum.inl (s,r)) (∑ t, rename (blockVariable t) (f t)) =
      pderiv (Sum.inl (s,r)) (rename (blockVariable s) (f s)) := by
  classical
  rw [map_sum, Finset.sum_eq_single s]
  · intro t _ hts
    exact JacobianBlocks.block_independent s t (Ne.symm hts) r (f t)
  · simp

/-- Explicit covariance of a normal-form contraction bracket under the actual
basis substitution used in HasBlockNormalForm. -/
theorem normalForm_bracket_covariance {N k m : ℕ} (F : CubicPolynomial N)
    (P : Trivector N) (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) ℂ)
    (hP : HasBlockTrivector P b)
    (hF : polynomialInBasis F b = ∑ s, rename (blockVariable s) (f s))
    (g h : CubicPolynomial N) :
    polynomialInBasis (bracketFromCoefficients (contractionCoefficients F P) g h) b =
      JacobianBlocks.blockBracket f (polynomialInBasis g b) (polynomialInBasis h b) := by
  classical
  rw [contraction_eq_directionalBlocks P b hP]
  change (polynomialBasisEquiv b) (∑ s,
    directionalJacobian (fun r => b (Sum.inl (s,r))) F g h) = _
  rw [map_sum]
  simp only [polynomialBasisEquiv_apply, polynomialInBasis_directionalJacobian, hF]
  unfold JacobianBlocks.blockBracket JacobianBlocks.sumBracket
  apply Finset.sum_congr rfl
  intro s _
  simp only [Jacobian.bracket, pderiv_block_sum]

/-- The entire converse direction of the affine classification, including
linear coordinate covariance. No smoothness assumption is needed. -/
theorem normalForm_satisfiesJacobi {N : ℕ} (F : CubicPolynomial N) (P : Trivector N)
    (h : HasBlockNormalForm F P) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) := by
  rcases h with ⟨k,m,_,_,b,f,_,hP,hF⟩
  intro g h l
  apply (polynomialBasisEquiv b).injective
  simpa only [map_add, map_zero, polynomialBasisEquiv_apply,
    normalForm_bracket_covariance F P b f hP hF] using
    JacobianBlocks.block_jacobi f (polynomialInBasis g b)
      (polynomialInBasis h b) (polynomialInBasis l b)

end NcCubic
