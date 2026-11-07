module
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.StdBasis
@[expose] public noncomputable section
open scoped TensorProduct
open Module
namespace NcCubic.Geometry.LineExteriorFrame
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Coordinates of the tensor square of a trivialized line. -/
def tensorCoordinate (e : M ≃ₗ[R] R) : M ⊗[R] M ≃ₗ[R] R :=
  (TensorProduct.congr e e).trans (TensorProduct.lid R R)

@[simp] theorem tensorCoordinate_tmul (e : M ≃ₗ[R] R) (v w : M) :
    tensorCoordinate e (v ⊗ₜ[R] w) = e v * e w := by
  simp [tensorCoordinate]

/-- The coordinate basis of a finite sum of one fixed line. -/
def sumBasis (e : M ≃ₗ[R] R) (N : ℕ) : Basis (Fin N) R (Fin N → M) :=
  (Pi.basisFun R (Fin N)).map (LinearEquiv.piCongrRight fun _ => e.symm)

@[simp] theorem sumBasis_apply (e : M ≃ₗ[R] R) (N : ℕ) (i j : Fin N) :
    sumBasis e N i j = if j = i then e.symm 1 else 0 := by
  by_cases h : j = i <;> simp [sumBasis, Pi.basisFun_apply, h]

@[simp] theorem sumBasis_coord (e : M ≃ₗ[R] R) (N : ℕ) (i : Fin N) (v : Fin N → M) :
    (sumBasis e N).coord i v = e (v i) := by
  simp [sumBasis, Basis.coord_apply]

@[simp] theorem sumBasis_eq_single (e : M ≃ₗ[R] R) (N : ℕ) (i : Fin N) :
    sumBasis e N i = Pi.single i (e.symm 1) := by
  ext j
  simp [sumBasis_apply, Pi.single_apply, eq_comm]

@[simp] theorem tensorCoordinate_symm_one (e : M ≃ₗ[R] R) :
    (tensorCoordinate e).symm 1 = e.symm 1 ⊗ₜ[R] e.symm 1 := by
  apply (tensorCoordinate e).injective
  simp

/-- A concrete coordinate equivalence for the second exterior power of a
finite sum of a line. The stalkwise trivialization will cancel in the actual
sheaf map, which is defined using only coordinate inclusions and wedge. -/
def equivalence (e : M ≃ₗ[R] R) (N : ℕ) :
    ⋀[R]^2 (Fin N → M) ≃ₗ[R] (Set.powersetCard (Fin N) 2 → M ⊗[R] M) :=
  (sumBasis e N).exteriorPower 2 |>.equivFun |>.trans
    (LinearEquiv.piCongrRight fun _ => (tensorCoordinate e).symm)

@[simp] theorem equivalence_ιMulti (e : M ≃ₗ[R] R) (N : ℕ)
    (v : Fin 2 → Fin N → M) (s : Set.powersetCard (Fin N) 2) :
    tensorCoordinate e (equivalence e N (exteriorPower.ιMulti R 2 v) s) =
      e (v 0 (Set.powersetCard.ofFinEmbEquiv.symm s 0)) *
        e (v 1 (Set.powersetCard.ofFinEmbEquiv.symm s 1)) -
      e (v 0 (Set.powersetCard.ofFinEmbEquiv.symm s 1)) *
        e (v 1 (Set.powersetCard.ofFinEmbEquiv.symm s 0)) := by
  simp only [equivalence, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    LinearEquiv.apply_symm_apply, Basis.equivFun_apply]
  rw [← Basis.coord_apply, exteriorPower.basis_coord,
    exteriorPower.ιMultiDual_apply_ιMulti]
  simp [Matrix.det_fin_two, -Basis.coord_apply]

/-- The reconstruction of a single coefficient is precisely its ordered
coordinate wedge, multiplied by the coordinate of the tensor coefficient. -/
theorem equivalence_symm_single (e : M ≃ₗ[R] R) (N : ℕ)
    (s : Set.powersetCard (Fin N) 2) (t : M ⊗[R] M) :
    (equivalence e N).symm (Pi.single s t) =
      tensorCoordinate e t • exteriorPower.ιMulti_family R 2 (sumBasis e N) s := by
  apply (equivalence e N).injective
  ext k
  apply (tensorCoordinate e).injective
  simp [equivalence, Basis.equivFun_apply, exteriorPower.basis_repr,
    Pi.single_apply, Finsupp.single_apply, eq_comm]
  split_ifs <;> simp_all

end NcCubic.Geometry.LineExteriorFrame
