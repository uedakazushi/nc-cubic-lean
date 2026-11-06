/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.PrimitiveWitness
public import NcCubic.RadicalWitness
public import NcCubic.LieObstruction
@[expose] public section
noncomputable section
namespace NcCubic.LieObstruction
open LieModule LieSubmodule Module
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K L M : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]

omit [CharZero K] [Module.Finite K M] in
/-- Irreducibility depends only on the image of the representation. -/
theorem irreducible_action_image [IsIrreducible K L M] :
    IsIrreducible K (toEnd K L M).range M := by
  let := nontrivial_of_isIrreducible K L M
  apply IsIrreducible.mk
  intro N hN
  let N' : LieSubmodule K L M :=
    { N.toSubmodule with
      lie_mem := by
        intro x m hm
        exact N.lie_mem (x := ⟨toEnd K L M x, x, rfl⟩) hm }
  have hN' : N' ≠ ⊥ := by
    intro hh
    apply hN
    apply LieSubmodule.toSubmodule_injective
    exact congrArg (fun S : LieSubmodule K L M => S.toSubmodule) hh
  let : Nontrivial N' := (LieSubmodule.nontrivial_iff_ne_bot K L M).mpr hN'
  have ht := N'.eq_top_of_isIrreducible K L M
  apply LieSubmodule.toSubmodule_injective
  exact congrArg (fun S : LieSubmodule K L M => S.toSubmodule) ht

omit [CharZero K] [Module.Finite K M] in
/-- A nonzero primitive vector is in the image of its raising operator
when its weight is nonzero. -/
theorem primitive_in_raising_image {h e f : L} (t : IsSl2Triple h e f)
    {μ : K} {v : M} (hp : t.HasPrimitiveVectorWith v μ) (hμ : μ ≠ 0) :
    ⁅e, μ⁻¹ • ⁅f,v⁆⁆ = v := by
  have he := hp.lie_e_pow_succ_toEnd_f 0
  simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero,
    sub_zero, one_mul, toEnd_apply_apply] at he
  rw [lie_smul, he, smul_smul, inv_mul_cancel₀ hμ, one_smul]

/-- Nontrivial irreducible trace-free actions admit the required nonzero
primitive weight in their faithful image. -/
theorem image_nonzero_primitive [IsAlgClosed K] [IsIrreducible K L M]
    (htrace : ∀ x : L, LinearMap.trace K M (toEnd K L M x) = 0)
    (hnontrivial : ∃ x : L, toEnd K L M x ≠ 0) :
    ∃ (h e f : (toEnd K L M).range) (t : IsSl2Triple h e f),
      ∃ (μ : K) (v : M), μ ≠ 0 ∧ t.HasPrimitiveVectorWith v μ := by
  let T := (toEnd K L M).range
  let : IsIrreducible K T M := irreducible_action_image
  let : LieAlgebra.HasTrivialRadical K T :=
    LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful K T M (by
      rintro ⟨_, x, rfl⟩
      exact htrace x)
  apply nonzero_primitive_of_semisimple
  obtain ⟨x,hx⟩ := hnontrivial
  exact ⟨⟨toEnd K L M x, x, rfl⟩, hx⟩
/-- A nonzero abelian minimal ideal in a perfect center-free Lie algebra
produces the actual ambient radical witness. -/
theorem radical_witness_of_abelian_atom [IsAlgClosed K] [Module.Finite K L]
    (hperfect : LieAlgebra.derivedSeries K L 1 = ⊤)
    (hcenter : LieAlgebra.center K L = ⊥)
    (I : LieIdeal K L) (hI : IsAtom I) [IsLieAbelian I] :
    ∃ h v e w : L, ∃ μ : K, v ≠ 0 ∧ μ ≠ 0 ∧
      ⁅h,v⁆ = μ • v ∧ ⁅e,w⁆ = v ∧ ⁅e,v⁆ = 0 ∧ ⁅v,w⁆ = 0 := by
  let : IsIrreducible K L I := irreducible_of_ideal_atom K L I hI
  have hn : ∃ x : L, toEnd K L I x ≠ 0 := by
    by_contra! hn
    have ht : I ≤ LieAlgebra.center K L := by
      intro v hv
      apply (LieModule.mem_maxTrivSubmodule K L L v).mpr
      intro x
      have hh := congrArg (fun A : Module.End K I => A ⟨v,hv⟩) (hn x)
      exact congrArg Subtype.val hh
    exact hI.1 (le_bot_iff.mp (hcenter ▸ ht))
  obtain ⟨h,e,f,t,μ,v,hμ,hp⟩ := image_nonzero_primitive
    (M := I) (trace_zero_of_perfect K L I hperfect) hn
  obtain ⟨h0,hh⟩ := h.property
  obtain ⟨e0,he⟩ := e.property
  change toEnd K L I h0 = (h : Module.End K I) at hh
  change toEnd K L I e0 = (e : Module.End K I) at he
  let w : I := μ⁻¹ • ⁅f,v⁆
  have hhv : ⁅h0,v⁆ = μ • v := by
    change (toEnd K L I h0) v = _
    rw [hh]
    exact hp.lie_h
  have hev : ⁅e0,v⁆ = 0 := by
    change (toEnd K L I e0) v = _
    rw [he]
    exact hp.lie_e
  have hew : ⁅e0,w⁆ = v := by
    change (toEnd K L I e0) w = _
    rw [he]
    exact primitive_in_raising_image t hp hμ
  refine ⟨h0, (v : L), e0, (w : L), μ, ?_, hμ, ?_, ?_, ?_, ?_⟩
  · intro hz
    exact hp.ne_zero (Subtype.ext hz)
  · exact congrArg Subtype.val hhv
  · exact congrArg Subtype.val hew
  · exact congrArg Subtype.val hev
  · exact congrArg Subtype.val (trivial_lie_zero I I v w)

/-- The compatibility and basepoint-free conditions force the radical to
vanish for every finite-dimensional perfect center-free complex-type algebra. -/
theorem radical_eq_bot_of_compatible_basepointFree [IsAlgClosed K] [Module.Finite K L]
    (hperfect : LieAlgebra.derivedSeries K L 1 = ⊤)
    (hcenter : LieAlgebra.center K L = ⊥)
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, Compatible H) (hfree : BasepointFree forms) :
    LieAlgebra.radical K L = ⊥ := by
  by_contra hr
  obtain ⟨I,hI,habelian⟩ := exists_abelian_atom_of_radical_ne_bot K L hr
  let := habelian
  obtain ⟨h,v,e,w,μ,hv,hμ,hhv,hew,hev,hvw⟩ :=
    radical_witness_of_abelian_atom hperfect hcenter I hI
  exact no_radical_witness forms hcompatible hfree h v e w μ hv hμ hhv hew hev hvw
end NcCubic.LieObstruction
