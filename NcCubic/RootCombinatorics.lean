/- Highest-root configurations in higher-rank irreducible root systems. -/
module
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Irreducible
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Module
import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
namespace NcCubic.RootCombinatorics
open RootPairing Module Submodule
variable {ι K M N : Type*} [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [Finite ι] (P : RootPairing ι K M N) [P.IsCrystallographic] [P.IsReduced]
  (b : P.Base)

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
/-- The sum of two positive roots is nonzero, even when it is not a root. -/
theorem positive_sum_ne_zero (θ α : ι) (hθ : b.IsPos θ) (hα : b.IsPos α) :
    P.root θ + P.root α ≠ 0 := by
  intro hz
  have heq : θ = P.reflectionPerm α α := by
    apply P.root.injective
    rw [RootPairing.root_reflectionPerm, P.reflection_apply_self]
    exact eq_neg_of_add_eq_zero_left hz
  have hh := b.height_reflectionPerm_self α
  change b.height (P.reflectionPerm α α) = -b.height α at hh
  have hθpos : 0 < b.height θ := hθ
  have hαpos : 0 < b.height α := hα
  rw [heq] at hθpos
  omega

omit [Finite ι] [P.IsCrystallographic] [P.IsReduced] in
/-- A maximal-height root cannot be increased by a positive root. -/
theorem no_successor_of_max_height (θ α : ι)
    (hmax : ∀ j, b.height j ≤ b.height θ) (hα : b.IsPos α) :
    P.root θ + P.root α ∉ Set.range P.root := by
  rintro ⟨j,hj⟩
  have heq := b.height_add hj
  have hjmax := hmax j
  have hαpos : 0 < b.height α := hα
  omega

omit [P.IsReduced] in
/-- Every positive non-simple root decomposes into positive roots. -/
theorem positive_non_simple_decomposition (θ : ι) (hθ : b.IsPos θ)
    (hn : θ ∉ b.support) :
    ∃ α β, b.IsPos α ∧ b.IsPos β ∧ P.root θ = P.root α + P.root β := by
  obtain ⟨β,hβ,hpair⟩ := hθ.exists_mem_support_pos_pairingIn
  rw [P.zero_lt_pairingIn_iff'] at hpair
  have hne : θ ≠ β := by intro h; subst θ; exact hn hβ
  obtain ⟨α,hα⟩ := P.root_sub_root_mem_of_pairingIn_pos hpair hne
  exact ⟨α,β,hθ.sub hβ hα,b.isPos_of_mem_support hβ,by rw [hα]; module⟩

/-- If a maximal-height root is simple, its line is invariant under every reflection. -/
theorem span_maximal_simple_invariant (θ : ι)
    (hmax : ∀ j, b.height j ≤ b.height θ) (hθ : θ ∈ b.support) :
    ∀ j, (K ∙ P.root θ) ∈ Module.End.invtSubmodule (P.reflection j) := by
  apply (b.forall_mem_support_invtSubmodule_iff (K ∙ P.root θ)).1
  intro j hj
  rw [Module.End.mem_invtSubmodule]
  intro x hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
  change P.reflection j (c • P.root θ) ∈ K ∙ P.root θ
  rw [map_smul]
  apply Submodule.smul_mem
  by_cases heq : j = θ
  · subst j
    rw [P.reflection_apply_self]
    exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))
  · have hle : P.pairingIn ℤ θ j ≤ 0 := b.pairingIn_le_zero_of_ne (Ne.symm heq) hθ hj
    have hzero : P.pairingIn ℤ θ j = 0 := by
      by_contra hn
      have hneg : P.pairingIn ℤ θ j < 0 := lt_of_le_of_ne hle hn
      have hadd := P.root_add_root_mem_of_pairingIn_neg hneg (b.root_ne_neg_of_ne hθ hj (Ne.symm heq))
      exact no_successor_of_max_height P b θ j hmax (b.isPos_of_mem_support hj) hadd
    have hz : P.pairing θ j = 0 := by
      rw [← P.algebraMap_pairingIn ℤ, hzero, map_zero]
    rw [P.reflection_apply_root, hz, zero_smul, sub_zero]
    exact Submodule.subset_span (Set.mem_singleton _)

/-- In irreducible rank at least two, a maximal-height root is not simple. -/
theorem maximal_not_simple [P.IsIrreducible] [FiniteDimensional K M]
    (hdim : 2 ≤ Module.finrank K M) (θ : ι)
    (hmax : ∀ j, b.height j ≤ b.height θ) : θ ∉ b.support := by
  intro hθ
  have hqtop : (K ∙ P.root θ) = ⊤ :=
    RootPairing.IsIrreducible.eq_top_of_invtSubmodule_reflection _
      (span_maximal_simple_invariant P b θ hmax hθ)
      (by
        intro hbot
        have hmem : P.root θ ∈ (K ∙ P.root θ) := Submodule.subset_span (Set.mem_singleton _)
        rw [hbot] at hmem
        exact P.ne_zero θ hmem)
  have hrank := finrank_span_singleton (K := K) (P.ne_zero θ)
  rw [hqtop, finrank_top] at hrank
  omega

/-- A higher-rank irreducible root system has a highest-root obstruction configuration. -/
theorem exists_highest_configuration [Nonempty ι] [P.IsIrreducible] [FiniteDimensional K M]
    (hdim : 2 ≤ Module.finrank K M) :
    ∃ θ α β, b.IsPos θ ∧ b.IsPos α ∧ b.IsPos β ∧
      P.root θ = P.root α + P.root β ∧
      P.root θ + P.root α ∉ Set.range P.root ∧
      P.root θ + P.root β ∉ Set.range P.root := by
  classical
  let := P.indexNeg
  obtain ⟨θ,hmax⟩ := Finite.exists_max b.height
  have hθ : b.IsPos θ := by
    let i : ι := Classical.arbitrary ι
    rcases RootPairing.Base.IsPos.or_neg b i with hi | hi
    · have h := hmax i
      exact lt_of_lt_of_le hi h
    · have h := hmax (-i)
      exact lt_of_lt_of_le hi h
  obtain ⟨α,β,hα,hβ,heq⟩ := positive_non_simple_decomposition P b θ hθ
    (maximal_not_simple P b hdim θ hmax)
  exact ⟨θ,α,β,hθ,hα,hβ,heq,
    no_successor_of_max_height P b θ α hmax hα,
    no_successor_of_max_height P b θ β hmax hβ⟩
end NcCubic.RootCombinatorics
