/- Finite three-dimensional simple ideals in compatible semisimple Lie algebras. -/
module
public import NcCubic.SimpleFactorDimension
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
namespace NcCubic.SemisimpleFactors
open LieAlgebra
variable {K A : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing A] [LieAlgebra K A] [FiniteDimensional K A] [IsSemisimple K A]

abbrev Index (K A : Type*) [CommRing K] [LieRing A] [LieAlgebra K A] :=
  {I : LieIdeal K A // IsAtom I}

instance finite_index : Finite (Index K A) :=
  (WellFoundedGT.finite_of_sSupIndep (IsSemisimple.sSupIndep_isAtom (R := K) (L := A))).to_subtype

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K A] in
theorem ideals_independent : iSupIndep (fun I : Index K A => I.val) :=
  (sSupIndep_iff _).1 (IsSemisimple.sSupIndep_isAtom (R := K) (L := A))

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K A] in
theorem ideals_sup_eq_top : (⨆ I : Index K A, I.val) = ⊤ := by
  simpa only [sSup_eq_iSup, iSup_subtype, Set.mem_ofPred_eq] using (IsSemisimple.sSup_atoms_eq_top (R := K) (L := A))

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K A] in
theorem subspaces_independent :
    iSupIndep (fun I : Index K A => (I.val : Submodule K A)) :=
  LieSubmodule.iSupIndep_toSubmodule.mpr ideals_independent

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K A] in
theorem subspaces_sup_eq_top :
    (⨆ I : Index K A, (I.val : Submodule K A)) = ⊤ :=
  LieSubmodule.iSup_toSubmodule_eq_top.mpr ideals_sup_eq_top

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K A] in
theorem ideals_commute (I J : Index K A) (hne : I ≠ J)
    (x : I.val) (y : J.val) : ⁅(x : A), (y : A)⁆ = 0 := by
  have hd := (ideals_independent (K := K) (A := A)).pairwiseDisjoint hne
  have hm : ⁅(x : A),(y : A)⁆ ∈ I.val ⊓ J.val :=
    ⟨lie_mem_left K A I.val (x : A) (y : A) x.property,
      lie_mem_right K A J.val (x : A) (y : A) y.property⟩
  exact hd.le_bot hm

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K A] in
theorem subspaces_isInternal [DecidableEq (Index K A)] :
    DirectSum.IsInternal (fun I : Index K A => (I.val : Submodule K A)) := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    subspaces_independent subspaces_sup_eq_top

omit [CharZero K] [IsAlgClosed K] [FiniteDimensional K A] in
theorem ideals_nonabelian (I : Index K A) : ¬ IsLieAbelian I.val :=
  IsSemisimple.non_abelian_of_isAtom I.val I.property

theorem simple_ideals_dim_three
    (forms : Set (A →ₗ[K] A →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, LieObstruction.Compatible H)
    (hfree : LieObstruction.BasepointFree forms) (I : Index K A) :
    Module.finrank K I.val = 3 :=
  SimpleFactorDimension.simple_ideal_finrank_eq_three I.val I.property forms hcompatible hfree
end NcCubic.SemisimpleFactors
