module
public import NcCubic.SupportFactorBasis
public import NcCubic.SupportSemisimple
public import NcCubic.SemisimpleFactors
@[expose] public section
noncomputable section
namespace NcCubic.TrivectorBlocks
open HessianCompatibility

/-- The full trivector assertion of paper Lemma 3.2: basepoint-free compatible
symmetric forms force independent normalized three-dimensional volume blocks. -/
theorem has_block_trivector_of_basepoint_free {N : ℕ} (P : Trivector N)
    (hfree : ∀ v : CoordinateSpace N, v ≠ 0 → ∃ H ∈ compatibleForms P, H v v ≠ 0) :
    ∃ (k m : ℕ) (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)), HasBlockTrivector P b := by
  classical
  obtain ⟨B, hmem, hB, hBr, hsemi⟩ := SupportConstruction.exists_support_semisimple_data P hfree
  let := SupportConstruction.supportLieRing P B (compatibleForms_isSymm P B hmem) hBr hmem.1
  let := SupportConstruction.supportLieAlgebra P B (compatibleForms_isSymm P B hmem) hBr hmem.1
  let := hsemi
  let U := SupportConstruction.support P
  let forms : Set (LinearMap.BilinForm ℂ U) :=
    Set.range (fun H : compatibleForms P => H.val.restrict U)
  have hcompatible : ∀ H ∈ forms, LieObstruction.Compatible H := by
    rintro H ⟨G, rfl⟩
    exact SupportConstruction.restricted_obstruction_compatible P B G.val
      (compatibleForms_isSymm P B hmem) hBr hmem.1 G.property.1
  have hbase : LieObstruction.BasepointFree forms := by
    intro w hw
    obtain ⟨H, hH, hHw⟩ := SupportConstruction.restricted_family_basepoint_free P hfree w hw
    exact ⟨H.restrict U, ⟨⟨H, hH⟩, rfl⟩, hHw⟩
  let ι := SemisimpleFactors.Index ℂ U
  let : Fintype ι := Fintype.ofFinite ι
  let enum : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let localBasis := fun i : ι => Module.finBasisOfFinrankEq ℂ i.val
    (SemisimpleFactors.simple_ideals_dim_three forms hcompatible hbase i)
  let hi := SemisimpleFactors.subspaces_isInternal (K := ℂ) (A := U)
  let allBasis := hi.collectedBasis localBasis
  let indexEquiv : (Σ _ : ι, Fin 3) ≃ (Fin (Fintype.card ι) × Fin 3) := {
    toFun := fun x => (enum x.1, x.2)
    invFun := fun x => ⟨enum.symm x.1, x.2⟩
    left_inv := by rintro ⟨i, j⟩; simp
    right_inv := by rintro ⟨s, j⟩; simp }
  let bU := allBasis.reindex indexEquiv
  let I := fun s : Fin (Fintype.card ι) => (enum.symm s).val.toSubmodule
  let bs := fun s : Fin (Fintype.card ι) => localBasis (enum.symm s)
  have hactive : ∀ s j, bU (s, j) = (bs s j : U) := by
    intro s j
    simp [bU, allBasis, indexEquiv, bs]
    exact congrFun (hi.collectedBasis_coe localBasis) ⟨enum.symm s, j⟩
  have hcomm : ∀ s t, s ≠ t → ∀ (x : I s) (y : I t),
      SupportConstruction.raisedBracket P B (x : U) (y : U) = 0 := by
    intro s t hst x y
    have hst' : enum.symm s ≠ enum.symm t := fun h => hst (enum.symm.injective h)
    have hz := SemisimpleFactors.ideals_commute (enum.symm s) (enum.symm t) hst' x y
    exact congrArg (fun z : U => (z : CoordinateSpace N)) hz
  have hn : ∀ s, ∃ x y : I s,
      SupportConstruction.raisedBracket P B (x : U) (y : U) ≠ 0 := by
    intro s
    by_contra! hz
    apply SemisimpleFactors.ideals_nonabelian (enum.symm s)
    refine ⟨?_⟩
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    exact hz x y
  obtain ⟨m, b, hb⟩ := normal_form_of_support_factor_basis P B
    (compatibleForms_isSymm P B hmem) hB hBr I bs bU hactive hcomm hn
  exact ⟨Fintype.card ι, m, b, hb⟩

end NcCubic.TrivectorBlocks
