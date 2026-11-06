/- Compatible basepoint-free forms force simple factors to have dimension three. -/
module
public import NcCubic.RootWitness
public import NcCubic.RankOneDimension
public import NcCubic.CompatibleRestriction
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.CartanExists
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section
noncomputable section
namespace NcCubic.SimpleFactorDimension
variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [LieAlgebra.IsSimple K L]

/-- The simple-factor assertion of paper Lemma 3.2, with no chosen root or Cartan data. -/
theorem finrank_eq_three
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, LieObstruction.Compatible H)
    (hfree : LieObstruction.BasepointFree forms) : Module.finrank K L = 3 := by
  obtain ⟨x,hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel K L
  let H := LieSubalgebra.engel K x
  let : H.IsCartanSubalgebra := hx
  exact RankOneDimension.finrank_eq_three_of_rank_one H
    (RootWitness.cartan_finrank_eq_one_of_compatible (K := K) (L := L) (H := H)
      forms hcompatible hfree)

/-- The conclusion applies to every finite-dimensional simple Lie subalgebra
whose inclusion into the ambient algebra is injective. -/
theorem simple_source_finrank_eq_three
    {A : Type*} [LieRing A] [LieAlgebra K A]
    (φ : L →ₗ⁅K⁆ A) (hφ : Function.Injective φ)
    (forms : Set (A →ₗ[K] A →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, LieObstruction.Compatible H)
    (hfree : LieObstruction.BasepointFree forms) : Module.finrank K L = 3 :=
  finrank_eq_three (LieObstruction.restrictedForms φ forms)
    (LieObstruction.restrictedForms_compatible φ forms hcompatible)
    (LieObstruction.restrictedForms_basepointFree φ hφ forms hfree)
end NcCubic.SimpleFactorDimension

namespace NcCubic.SimpleFactorDimension
variable {K A : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing A] [LieAlgebra K A] [FiniteDimensional K A] [LieAlgebra.IsSemisimple K A]

/-- Every simple ideal in a semisimple algebra with a basepoint-free compatible
family has dimension three. The family is genuinely restricted along inclusion. -/
theorem simple_ideal_finrank_eq_three (I : LieIdeal K A) (hI : IsAtom I)
    (forms : Set (A →ₗ[K] A →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, LieObstruction.Compatible H)
    (hfree : LieObstruction.BasepointFree forms) : Module.finrank K I = 3 := by
  let : LieAlgebra.IsSimple K I := LieAlgebra.IsSemisimple.isSimple_of_isAtom I hI
  exact simple_source_finrank_eq_three I.incl I.incl_injective forms hcompatible hfree
end NcCubic.SimpleFactorDimension
