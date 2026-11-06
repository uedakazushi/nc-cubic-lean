module
public import NcCubic.BlockContraction
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic
open MvPolynomial
open scoped BigOperators

/-- A constant alternating tensor contracted against a potential's gradient. -/
def tensorBracket {σ : Type*} [Fintype σ] (T : σ → σ → σ → ℂ)
    (F f g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ i, ∑ j, ∑ a, C (T i j a) * pderiv a F * pderiv i f * pderiv j g

theorem tensorBracket_zero {σ : Type*} [Fintype σ] (F f g : MvPolynomial σ ℂ) :
    tensorBracket (fun _ _ _ => 0) F f g = 0 := by
  simp [tensorBracket]

theorem tensorBracket_add {σ : Type*} [Fintype σ] (T U : σ → σ → σ → ℂ)
    (F f g : MvPolynomial σ ℂ) :
    tensorBracket (fun i j a => T i j a + U i j a) F f g =
      tensorBracket T F f g + tensorBracket U F f g := by
  simp [tensorBracket, add_mul, Finset.sum_add_distrib]

theorem tensorBracket_smul {σ : Type*} [Fintype σ] (c : ℂ)
    (T : σ → σ → σ → ℂ) (F f g : MvPolynomial σ ℂ) :
    tensorBracket (fun i j a => c * T i j a) F f g = C c * tensorBracket T F f g := by
  simp [tensorBracket, map_mul, mul_assoc, Finset.mul_sum]

def finiteDirectionalDerivative {σ : Type*} [Fintype σ] (v : (σ → ℂ)) (F : MvPolynomial σ ℂ) :
    MvPolynomial σ ℂ := ∑ i, C (v i) * pderiv i F

/-- A Jacobian bracket expressed in three constant vector directions. -/
def finiteDirectionalJacobian {σ : Type*} [Fintype σ] (v : Fin 3 → (σ → ℂ))
    (F f g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  (finiteDirectionalDerivative (v 0) f * finiteDirectionalDerivative (v 1) g -
    finiteDirectionalDerivative (v 1) f * finiteDirectionalDerivative (v 0) g) * finiteDirectionalDerivative (v 2) F +
  (finiteDirectionalDerivative (v 1) f * finiteDirectionalDerivative (v 2) g -
    finiteDirectionalDerivative (v 2) f * finiteDirectionalDerivative (v 1) g) * finiteDirectionalDerivative (v 0) F +
  (finiteDirectionalDerivative (v 2) f * finiteDirectionalDerivative (v 0) g -
    finiteDirectionalDerivative (v 0) f * finiteDirectionalDerivative (v 2) g) * finiteDirectionalDerivative (v 1) F

/-- Determinant expansion of one volume tensor's contraction bracket. -/
theorem finite_determinant_contraction {σ : Type*} [Fintype σ] (v : Fin 3 → (σ → ℂ))
    (F f g : MvPolynomial σ ℂ) :
    (∑ i, ∑ j, ∑ a,
      C (Matrix.det (Matrix.of (fun r c : Fin 3 => (![(fun v => v i), (fun v => v j),
        (fun v => v a)] r) (v c)))) * pderiv i f * pderiv j g * pderiv a F) =
      finiteDirectionalJacobian v F f g := by
  classical
  have hd (i j a : σ) :
      Matrix.det (Matrix.of (fun r c : Fin 3 =>
        (![(fun v => v i), (fun v => v j), (fun v => v a)] r) (v c))) =
      v 0 i * v 1 j * v 2 a - v 0 i * v 2 j * v 1 a -
      v 1 i * v 0 j * v 2 a + v 1 i * v 2 j * v 0 a +
      v 2 i * v 0 j * v 1 a - v 2 i * v 1 j * v 0 a := by
    rw [Matrix.det_fin_three]
    rfl
  simp only [hd, map_add, map_sub, map_mul]
  unfold finiteDirectionalJacobian finiteDirectionalDerivative
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


/-- The coefficient convention for `tensorBracket` agrees with the determinant expansion. -/
theorem tensorBracket_determinant {σ : Type*} [Fintype σ]
    (v : Fin 3 → (σ → ℂ)) (F f g : MvPolynomial σ ℂ) :
    tensorBracket (fun i j a => Matrix.det (Matrix.of (fun r c : Fin 3 =>
      (![fun w => w i, fun w => w j, fun w => w a] r) (v c)))) F f g =
      finiteDirectionalJacobian v F f g := by
  classical
  rw [← finite_determinant_contraction]
  unfold tensorBracket
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Original coordinates are the special case indexed by `Fin N`. -/
theorem tensorBracket_contraction {N : ℕ} (P : Trivector N)
    (F f g : CubicPolynomial N) :
    tensorBracket (trivectorCoefficient P) F f g =
      bracketFromCoefficients (contractionCoefficients F P) f g := by
  simp only [tensorBracket, bracketFromCoefficients, contractionCoefficients,
    Finset.sum_mul]

end NcCubic
