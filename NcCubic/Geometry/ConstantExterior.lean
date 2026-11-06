/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.KoszulCoordinates
public import NcCubic.ExteriorComparison
import Mathlib.Tactic.FinCases
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.ConstantExterior
open MvPolynomial
open scoped BigOperators
open KoszulCoordinates
variable {N : ℕ}

/-- The scalar trivector corresponding to constant exterior basis coordinates. -/
def constantTrivector (a : Set.powersetCard (Fin N) 3 → ℂ) : Trivector N :=
  exteriorTrivectorEquiv N (∑ s, a s • (Pi.basisFun ℂ (Fin N)).exteriorPower 3 s)

/-- The same constant tensor in the exterior power over the polynomial ring. -/
def polynomialTrivector (a : Set.powersetCard (Fin N) 3 → ℂ) :
    ⋀[CubicPolynomial N]^3 (Fin N → CubicPolynomial N) :=
  ∑ s, (C (a s) : CubicPolynomial N) • (Pi.basisFun (CubicPolynomial N) (Fin N)).exteriorPower 3 s

/-- The alternating-on-covectors convention agrees with exterior coordinates. -/
theorem coefficient_eq_trivectorCoefficient
    (x : ⋀[ℂ]^3 (CoordinateSpace N)) (i j a : Fin N) :
    coefficient ![i,j,a] x = trivectorCoefficient (exteriorTrivectorEquiv N x) i j a := by
  have hx : x ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ 3
      (M := CoordinateSpace N))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    rw [coefficient_ιMulti]
    simp only [trivectorCoefficient, exteriorTrivectorEquiv_volume]
    have hm : Matrix.of (fun r c : Fin 3 => v r (![i,j,a] c)) =
        Matrix.transpose (Matrix.of (fun r c : Fin 3 => (![coordinateCovector i,coordinateCovector j,
          coordinateCovector a] r) (v c))) := by
      funext r c
      fin_cases c <;> rfl
    change (Matrix.of (fun r c : Fin 3 => v r (![i,j,a] c))).det = _
    rw [hm, Matrix.det_transpose]
    rfl
  | zero => simp [trivectorCoefficient]
  | add x y _ _ ihx ihy =>
    simp only [map_add, trivectorCoefficient, add_apply] at ihx ihy ⊢
    exact congrArg₂ (· + ·) ihx ihy
  | smul c x _ ih =>
    simp only [map_smul, trivectorCoefficient, smul_apply, smul_eq_mul] at ih ⊢
    exact congrArg (c * ·) ih

/-- Extension of the coefficient field commutes with each exterior basis
coordinate evaluation. -/
theorem coefficient_basis_map (s : Set.powersetCard (Fin N) 3) (i j a : Fin N) :
    coefficient ![i,j,a]
      ((Pi.basisFun (CubicPolynomial N) (Fin N)).exteriorPower 3 s) =
    C (coefficient ![i,j,a] ((Pi.basisFun ℂ (Fin N)).exteriorPower 3 s)) := by
  classical
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    coefficient_ιMulti]
  change (Matrix.of (fun r c : Fin 3 =>
    (Pi.basisFun (CubicPolynomial N) (Fin N))
      (Set.powersetCard.ofFinEmbEquiv.symm s r) (![i,j,a] c))).det =
    C ((Matrix.of (fun r c : Fin 3 => (Pi.basisFun ℂ (Fin N))
      (Set.powersetCard.ofFinEmbEquiv.symm s r) (![i,j,a] c))).det)
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro r c
  simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Pi.basisFun_apply, Pi.single_apply]
  split_ifs <;> simp_all

/-- Polynomial exterior coordinates of a constant tensor are exactly the
constant polynomial coefficients of its original scalar trivector. -/
theorem coefficient_polynomialTrivector
    (a : Set.powersetCard (Fin N) 3 → ℂ) (i j k : Fin N) :
    coefficient ![i,j,k] (polynomialTrivector a) =
      C (trivectorCoefficient (constantTrivector a) i j k) := by
  classical
  unfold constantTrivector
  rw [← coefficient_eq_trivectorCoefficient]
  simp only [polynomialTrivector]
  simp only [map_sum, map_smul, smul_eq_mul, map_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [coefficient_basis_map]
/-- The genuine Koszul differential of the polynomial exterior tensor is
exactly the original contraction array, with the same sign convention. -/
theorem coefficient_d_polynomialTrivector (F : CubicPolynomial N)
    (a : Set.powersetCard (Fin N) 3 → ℂ) (i j : Fin N) :
    coefficient ![i,j]
      (Koszul.d (Koszul.seqDual (fun k => pderiv k F)) 2 (polynomialTrivector a)) =
      contractionCoefficients F (constantTrivector a) i j := by
  rw [coefficient_d2]
  simp only [coefficient_polynomialTrivector, contractionCoefficients]
  apply Finset.sum_congr rfl
  intro k _
  have hcyc : trivectorCoefficient (constantTrivector a) k i j =
      trivectorCoefficient (constantTrivector a) i j k := by
    rw [trivectorCoefficient_swap_last (constantTrivector a) j i k,
      trivectorCoefficient_swap_first (constantTrivector a) i j k, neg_neg]
  rw [hcyc, mul_comm]
end NcCubic.Geometry.ConstantExterior
