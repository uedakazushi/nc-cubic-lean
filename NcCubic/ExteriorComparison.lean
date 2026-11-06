/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Coordinates
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas
@[expose] public section
noncomputable section
namespace NcCubic

/-- The finite-dimensional exterior tensor and alternating-on-covectors models agree. -/
def exteriorTrivectorEquiv (N : ℕ) :
    (⋀[ℂ]^3 (CoordinateSpace N)) ≃ₗ[ℂ] Trivector N :=
  (LinearEquiv.ofBijective
    (exteriorPower.map 3 (Module.evalEquiv ℂ (CoordinateSpace N)).toLinearMap)
    ⟨exteriorPower.map_injective_field (Module.evalEquiv ℂ (CoordinateSpace N)).injective,
      exteriorPower.map_surjective (Module.evalEquiv ℂ (CoordinateSpace N)).surjective⟩).trans
    ((LinearEquiv.ofBijective (exteriorPower.pairingDual ℂ (Covector N) 3)
      (exteriorPower.bijective_pairingDual ℂ (Covector N) 3)).trans
      exteriorPower.alternatingMapLinearEquiv.symm)

/-- A decomposable exterior tensor acts by the determinant of covector evaluations. -/
theorem exteriorTrivectorEquiv_volume {N : ℕ} (v : Fin 3 → CoordinateSpace N)
    (α : Fin 3 → Covector N) :
    exteriorTrivectorEquiv N (exteriorPower.ιMulti ℂ 3 v) α =
      Matrix.det (fun i j : Fin 3 => α i (v j)) := by
  simp [exteriorTrivectorEquiv, exteriorPower.alternatingMapLinearEquiv_symm_apply,
    LinearMap.compAlternatingMap_apply, exteriorPower.pairingDual_ιMulti_ιMulti,
    Function.comp_def]
  rfl

/-- The determinant contract is precisely the sum of exterior volume tensors. -/
theorem hasBlockTrivector_iff_exterior {N k m : ℕ} (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) :
    HasBlockTrivector P b ↔ (exteriorTrivectorEquiv N).symm P =
      ∑ s : Fin k, exteriorPower.ιMulti ℂ 3 (fun j => b (Sum.inl (s, j))) := by
  classical
  rw [LinearEquiv.symm_apply_eq]
  simp only [map_sum]
  constructor
  · intro h
    apply AlternatingMap.ext
    intro α
    simpa only [sum_apply, exteriorTrivectorEquiv_volume] using h α
  · intro h α
    have hh := congrArg (fun Q : Trivector N => Q α) h
    simpa only [sum_apply, exteriorTrivectorEquiv_volume] using hh

/-- Tensor transport agrees with precomposition of all covectors by the dual map. -/
theorem exteriorTrivectorEquiv_natural {N M : ℕ}
    (A : CoordinateSpace N →ₗ[ℂ] CoordinateSpace M)
    (x : ⋀[ℂ]^3 (CoordinateSpace N)) :
    exteriorTrivectorEquiv M (exteriorPower.map 3 A x) =
      (exteriorTrivectorEquiv N x).compLinearMap A.dualMap := by
  have hx : x ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ 3 (M := CoordinateSpace N))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    ext α
    simp only [exteriorPower.map_apply_ιMulti, exteriorTrivectorEquiv_volume,
      AlternatingMap.compLinearMap_apply]
    rfl
  | zero =>
    ext α
    simp
  | add x y hx hy ihx ihy =>
    simp only [map_add, ihx, ihy, AlternatingMap.add_compLinearMap]
  | smul c x hx ih =>
    ext α
    simp only [map_smul, ih, AlternatingMap.compLinearMap_apply, smul_apply]

theorem dualBasis_standard_eq_coordinate {N : ℕ} (i : Fin N) :
    (Pi.basisFun ℂ (Fin N)).dualBasis i = coordinateCovector i := by
  apply LinearMap.ext
  intro x
  simp [coordinateCovector]

/-- The coefficient tensor determines the full alternating trilinear map. -/
theorem trivectorCoefficient_ext {N : ℕ} (P Q : Trivector N)
    (h : ∀ i j a, trivectorCoefficient P i j a = trivectorCoefficient Q i j a) : P = Q := by
  apply (Pi.basisFun ℂ (Fin N)).dualBasis.ext_alternating
  intro v hv
  simp only [dualBasis_standard_eq_coordinate]
  have hp : (fun i : Fin 3 => coordinateCovector (v i)) =
      ![coordinateCovector (v 0), coordinateCovector (v 1), coordinateCovector (v 2)] := by
    funext i; fin_cases i <;> rfl
  rw [hp]
  exact h (v 0) (v 1) (v 2)
end NcCubic
