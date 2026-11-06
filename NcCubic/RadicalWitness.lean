/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Scalar-action proof adapted from Mathlib.Algebra.Lie.Semisimple.Lemmas,
Copyright (c) 2025 Oliver Nash. Released under Apache 2.0 license as described
in the dependency LICENSE; original author: Oliver Nash.
-/
module
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
@[expose] public section
noncomputable section

namespace NcCubic.LieObstruction
open LieModule LieSubmodule Module

variable (K L M : Type*) [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M] [IsIrreducible K L M] [IsTriangularizable K L M]

/-- The radical acts by scalars in an irreducible representation, including
nonfaithful representations such as an abelian ideal's adjoint module. -/
theorem radical_acts_by_scalars :
    ∃ χ : Module.Dual K (LieAlgebra.radical K L),
      ∀ x : LieAlgebra.radical K L,
        toEnd K L M (x : L) = χ x • LinearMap.id := by
  have := nontrivial_of_isIrreducible K L M
  obtain ⟨χ, hχ⟩ :=
    exists_nontrivial_weightSpace_of_isSolvable K (LieAlgebra.radical K L) M
  let N : LieSubmodule K L M := weightSpaceOfIsLieTower K M χ
  have hN : Nontrivial N := hχ
  have htop : N = ⊤ := N.eq_top_of_isIrreducible K L M
  refine ⟨χ, fun x => ?_⟩
  ext m
  have hm : ∀ y : LieAlgebra.radical K L, ⁅(y : L), m⁆ = χ y • m := by
    simpa [N, weightSpaceOfIsLieTower, mem_weightSpace] using
      (htop ▸ mem_top m : m ∈ N)
  simpa using hm x

/-- Trace-free irreducible representations kill the solvable radical.
No faithfulness assumption is imposed on the representation. -/
theorem radical_acts_trivially_of_trace_zero
    (htrace : ∀ x : L, LinearMap.trace K M (toEnd K L M x) = 0)
    (x : LieAlgebra.radical K L) : toEnd K L M (x : L) = 0 := by
  obtain ⟨χ, hχ⟩ := radical_acts_by_scalars K L M
  have hn : finrank K M ≠ 0 :=
    (finrank_pos_iff.mpr (nontrivial_of_isIrreducible K L M)).ne'
  have hc : χ x = 0 := by
    have ht := htrace (x : L)
    rw [hχ x] at ht
    simpa [hn] using ht
  simp [hχ x, hc]

omit [CharZero K] [Module.Finite K L] [Module.Finite K M]
  [IsIrreducible K L M] [IsTriangularizable K L M] in
/-- Every finite-dimensional representation of a perfect Lie algebra is trace-free. -/
theorem trace_zero_of_perfect
    (hperfect : LieAlgebra.derivedSeries K L 1 = ⊤) (x : L) :
    LinearMap.trace K M (toEnd K L M x) = 0 := by
  have hx : x ∈ Submodule.span K {⁅a, b⁆ | (a : L) (b : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq, hperfect]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, b, rfl⟩ := hy
    simp [LieHom.map_lie]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

/-- The radical annihilates every irreducible representation of a perfect
Lie algebra. This applies to the minimal abelian ideal in the classification. -/
theorem radical_acts_trivially_of_perfect
    (hperfect : LieAlgebra.derivedSeries K L 1 = ⊤)
    (x : LieAlgebra.radical K L) : toEnd K L M (x : L) = 0 :=
  radical_acts_trivially_of_trace_zero K L M (trace_zero_of_perfect K L M hperfect) x

end NcCubic.LieObstruction

namespace NcCubic.LieObstruction

/-- A nonzero solvable radical contains a nonzero minimal abelian ideal.
The minimality is with respect to ideals of the ambient Lie algebra. -/
theorem exists_abelian_atom_of_radical_ne_bot
    (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L]
    (h : LieAlgebra.radical K L ≠ ⊥) :
    ∃ I : LieIdeal K L, IsAtom I ∧ IsLieAbelian I := by
  classical
  have hex : ∃ J : LieIdeal K L, J ≠ ⊥ ∧ IsLieAbelian J := by
    by_contra! hn
    have ht : LieAlgebra.HasTrivialRadical K L :=
      (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals K L).mpr
        (fun J hJ => by
          by_contra hne
          exact hn J hne hJ)
    exact h ht.radical_eq_bot
  obtain ⟨J, hJ, habelian⟩ := hex
  obtain ⟨I, hI, hIJ⟩ := (eq_bot_or_exists_atom_le J).resolve_left hJ
  refine ⟨I, hI, ?_⟩
  let _ := habelian
  constructor
  intro x y
  ext
  have hz : (⁅(⟨x, hIJ x.2⟩ : J), ⟨y, hIJ y.2⟩⁆ : J) = 0 :=
    trivial_lie_zero _ _ _ _
  simpa only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket,
    ZeroMemClass.coe_zero] using congrArg Subtype.val hz

end NcCubic.LieObstruction

namespace NcCubic.LieObstruction

/-- An ideal minimal among nonzero ambient ideals is an irreducible
module for the ambient adjoint action. -/
theorem irreducible_of_ideal_atom (K L : Type*) [Field K] [LieRing L]
    [LieAlgebra K L] (I : LieIdeal K L) (hI : IsAtom I) :
    LieModule.IsIrreducible K L I := by
  let _ : Nontrivial I :=
    (LieSubmodule.nontrivial_iff_ne_bot K L L).mpr hI.1
  apply LieModule.IsIrreducible.mk (R := K) (L := L) (M := I)
  intro N hN
  have hinj := LieSubmodule.map_injective_of_injective
    (f := (LieSubmodule.incl I)) (Subtype.coe_injective)
  have hmap : N.map (LieSubmodule.incl I) ≠ ⊥ := by
    intro hz
    apply hN
    apply hinj
    simpa using hz
  have heq : N.map (LieSubmodule.incl I) = I :=
    (hI.le_iff_eq hmap).mp LieSubmodule.map_incl_le
  apply hinj
  simpa using heq

end NcCubic.LieObstruction
