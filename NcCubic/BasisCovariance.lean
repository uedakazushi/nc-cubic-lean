/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.ContractionLinearity
public import NcCubic.ExteriorComparison
@[expose] public section
noncomputable section
set_option maxHeartbeats 1600000
namespace NcCubic
open MvPolynomial
open scoped BigOperators

/-- Contract in the coordinates dual to an arbitrary basis. -/
def basisContractionBracket {N k m : ℕ} (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (F f g : MvPolynomial (BlockIndex k m) ℂ) :=
  tensorBracket (fun i j a => P ![b.dualBasis i, b.dualBasis j, b.dualBasis a]) F f g

private def tensorBracketLinear {N : ℕ} {σ : Type*} [Fintype σ]
    (α : σ → Covector N) (F f g : MvPolynomial σ ℂ) :
    Trivector N →ₗ[ℂ] MvPolynomial σ ℂ where
  toFun P := tensorBracket (fun i j a => P ![α i, α j, α a]) F f g
  map_add' P Q := by simpa only [add_apply] using (tensorBracket_add
    (fun i j a => P ![α i, α j, α a]) (fun i j a => Q ![α i, α j, α a]) F f g)
  map_smul' c P := by
    simp only [smul_apply, smul_eq_mul]
    rw [tensorBracket_smul]
    simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, RingHom.id_apply]

private theorem volume_basis_covariance {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (t : Fin 3 → BlockIndex k m) (F f g : CubicPolynomial N) :
    basisContractionBracket (exteriorTrivectorEquiv N
      (exteriorPower.ιMulti ℂ 3 (fun r => b (t r)))) b
      (polynomialInBasis F b) (polynomialInBasis f b) (polynomialInBasis g b) =
    polynomialInBasis (tensorBracket (trivectorCoefficient (exteriorTrivectorEquiv N
      (exteriorPower.ιMulti ℂ 3 (fun r => b (t r))))) F f g) b := by
  classical
  have hdual (i j : BlockIndex k m) : b.dualBasis i (b j) =
      (Pi.single j 1 : BlockIndex k m → ℂ) i := by simp [Pi.single_apply, Finsupp.single_apply, eq_comm]
  have ht : (fun i j a => (exteriorTrivectorEquiv N
      (exteriorPower.ιMulti ℂ 3 (fun r => b (t r))))
        ![b.dualBasis i, b.dualBasis j, b.dualBasis a]) =
      (fun i j a => Matrix.det (Matrix.of (fun r c : Fin 3 =>
        (![fun w => w i, fun w => w j, fun w => w a] r)
          (Pi.single (t c) 1 : BlockIndex k m → ℂ)))) := by
    funext i j a
    rw [exteriorTrivectorEquiv_volume]
    congr 1
    funext r c
    fin_cases r <;> exact hdual _ _
  have hs : trivectorCoefficient (exteriorTrivectorEquiv N
      (exteriorPower.ιMulti ℂ 3 (fun r => b (t r)))) =
      (fun i j a => Matrix.det (Matrix.of (fun r c : Fin 3 =>
        (![fun w => w i, fun w => w j, fun w => w a] r) (b (t c))))) := by
    funext i j a
    simp only [trivectorCoefficient, exteriorTrivectorEquiv_volume]
    rfl
  unfold basisContractionBracket
  rw [ht, hs, tensorBracket_determinant, tensorBracket_determinant]
  have he (i : BlockIndex k m) (H : MvPolynomial (BlockIndex k m) ℂ) :
      finiteDirectionalDerivative (Pi.single i 1) H = pderiv i H := by
    simp [finiteDirectionalDerivative, Pi.single_apply]
  simp only [finiteDirectionalJacobian, he]
  change _ = polynomialInBasis (directionalJacobian (fun r => b (t r)) F f g) b
  simp only [directionalJacobian, polynomialInBasis, map_add, map_sub, map_mul]
  change _ =
    (polynomialInBasis (directionalDerivative (b (t 0)) f) b *
    polynomialInBasis (directionalDerivative (b (t 1)) g) b -
    polynomialInBasis (directionalDerivative (b (t 1)) f) b *
    polynomialInBasis (directionalDerivative (b (t 0)) g) b) *
    polynomialInBasis (directionalDerivative (b (t 2)) F) b +
    (polynomialInBasis (directionalDerivative (b (t 1)) f) b *
    polynomialInBasis (directionalDerivative (b (t 2)) g) b -
    polynomialInBasis (directionalDerivative (b (t 2)) f) b *
    polynomialInBasis (directionalDerivative (b (t 1)) g) b) *
    polynomialInBasis (directionalDerivative (b (t 0)) F) b +
    (polynomialInBasis (directionalDerivative (b (t 2)) f) b *
    polynomialInBasis (directionalDerivative (b (t 0)) g) b -
    polynomialInBasis (directionalDerivative (b (t 0)) f) b *
    polynomialInBasis (directionalDerivative (b (t 2)) g) b) *
    polynomialInBasis (directionalDerivative (b (t 1)) F) b
  simp only [polynomialInBasis_directionalDerivative]
  rfl

/-- Arbitrary constant trivectors, potentials and arguments transform covariantly. -/
theorem basisContractionBracket_covariance {N k m : ℕ} (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (F f g : CubicPolynomial N) :
    basisContractionBracket P b (polynomialInBasis F b)
      (polynomialInBasis f b) (polynomialInBasis g b) =
    polynomialInBasis (bracketFromCoefficients (contractionCoefficients F P) f g) b := by
  let L := (tensorBracketLinear (fun i => b.dualBasis i)
    (polynomialInBasis F b) (polynomialInBasis f b) (polynomialInBasis g b)).comp
      (exteriorTrivectorEquiv N).toLinearMap
  let R := ((polynomialBasisEquiv b).toLinearMap.comp
    (tensorBracketLinear (coordinateCovector (N := N)) F f g)).comp
      (exteriorTrivectorEquiv N).toLinearMap
  have h : L = R := by
    apply exteriorPower.linearMap_ext
    apply b.ext_alternating
    intro t _
    exact volume_basis_covariance b t F f g
  have hh := LinearMap.congr_fun h ((exteriorTrivectorEquiv N).symm P)
  change basisContractionBracket ((exteriorTrivectorEquiv N)
    ((exteriorTrivectorEquiv N).symm P)) b (polynomialInBasis F b)
      (polynomialInBasis f b) (polynomialInBasis g b) =
    polynomialInBasis (tensorBracket (trivectorCoefficient ((exteriorTrivectorEquiv N)
      ((exteriorTrivectorEquiv N).symm P))) F f g) b at hh
  simpa only [LinearEquiv.apply_symm_apply, tensorBracket_contraction] using hh
end NcCubic
