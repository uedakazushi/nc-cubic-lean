module
public import NcCubic.FactorBasis
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.Dimension.Free
@[expose] public section
noncomputable section
namespace NcCubic.TrivectorBlocks

/-- Distinct disjoint Lie ideals commute, stated on their actual vector subtypes. -/
theorem ideals_commute_of_disjoint
    {F L : Type*} [Field F] [LieRing L] [LieAlgebra F L]
    (I J : LieIdeal F L) (hdis : Disjoint I.toSubmodule J.toSubmodule)
    (x : I) (y : J) : ⁅(x : L), (y : L)⁆ = 0 := by
  have hm : ⁅(x : L), (y : L)⁆ ∈ I.toSubmodule ⊓ J.toSubmodule :=
    ⟨lie_mem_left F L I x y x.property, lie_mem_right F L J x y y.property⟩
  have hz := hdis.le_bot hm
  simpa using hz

/-- Actual finite nonabelian ideal factors of dimension three, with a central
complement, supply all the data of L5. -/
theorem normal_form_of_internal_lie_ideals
    {N : ℕ} (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate) (hK : HessianCompatibility.Compatible P B) :
    let := SupportConstruction.lieRing P B hsym hB hK
    let := SupportConstruction.lieAlgebra P B hsym hB hK
    ∀ {k m : ℕ} (I : Fin k → LieIdeal ℂ (CoordinateSpace N))
      (Z : Submodule ℂ (CoordinateSpace N)),
      DirectSum.IsInternal (Sum.elim (fun s => (I s).toSubmodule) (fun _ : PUnit => Z)) →
      (∀ s, Module.finrank ℂ (I s) = 3) → Module.Basis (Fin m) ℂ Z →
      Z ≤ (LieAlgebra.center ℂ (CoordinateSpace N)).toSubmodule →
      (∀ s, ¬ IsLieAbelian (I s)) →
      ∃ b' : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N), HasBlockTrivector P b' := by
  let := SupportConstruction.lieRing P B hsym hB hK
  let := SupportConstruction.lieAlgebra P B hsym hB hK
  dsimp only
  intro k m I Z h hdim bz hZ hnonabelian
  classical
  let bs := fun s => Module.finBasisOfFinrankEq ℂ (I s) (hdim s)
  apply normal_form_of_internal_commuting_factors P B hsym hB
    (fun s => (I s).toSubmodule) Z h bs bz
  · intro z y
    have hz : ∀ y : CoordinateSpace N, ⁅y, (z : CoordinateSpace N)⁆ = 0 :=
      (LieModule.mem_maxTrivSubmodule ℂ (CoordinateSpace N) (CoordinateSpace N) z).mp (hZ z.property)
    change ⁅(z : CoordinateSpace N), y⁆ = 0
    rw [← lie_skew, hz, neg_zero]
  · intro s t hst x y
    have hst' : (Sum.inl s : Fin k ⊕ PUnit) ≠ Sum.inl t :=
      fun he => hst (Sum.inl.inj he)
    have hd := h.submodule_iSupIndep.pairwiseDisjoint hst'
    exact ideals_commute_of_disjoint (I s) (I t) hd x y
  · intro s
    by_contra! hz
    apply hnonabelian s
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    exact hz x y

end NcCubic.TrivectorBlocks
