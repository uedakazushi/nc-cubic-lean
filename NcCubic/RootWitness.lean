/- Root-space construction of the highest-root obstruction witness. -/
module
public import NcCubic.LieObstruction
public import Mathlib.Algebra.Lie.Weights.IsSimple
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import NcCubic.RootCombinatorics

@[expose] public section
noncomputable section
namespace NcCubic.RootWitness
open LieModule LieAlgebra LieAlgebra.IsKilling
variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- A root which is a sum of two roots but has no successors in their directions
produces the explicit highest-root witness. The existence of such a root
configuration in every higher-rank simple factor is a separate obligation. -/
theorem exists_highest_witness (α β θ : Weight K H L)
    (hα : α.IsNonZero) (hθ : θ.IsNonZero)
    (hsum : (θ : H → K) = α + β)
    (hαθ : rootSpace H (α + θ) = ⊥) (hβθ : rootSpace H (β + θ) = ⊥) :
    ∃ a b h v : L, ∃ c : K,
      v ≠ 0 ∧ c ≠ 0 ∧ ⁅a, b⁆ = v ∧ ⁅h, v⁆ = c • v ∧
        ⁅a, v⁆ = 0 ∧ ⁅b, v⁆ = 0 := by
  have hsumSpace : rootSpace H (α + β) ≠ ⊥ := by
    rw [← hsum]
    exact θ.genWeightSpace_ne_bot
  obtain ⟨a, ha, b, hb, hab⟩ :=
    LieAlgebra.IsKilling.exists_mem_rootSpace_lie_ne_zero hα hsumSpace
  have hv : ⁅a,b⁆ ∈ rootSpace H θ := by
    rw [hsum]
    exact lie_mem_genWeightSpace_of_mem_genWeightSpace ha hb
  have hav : ⁅a,⁅a,b⁆⁆ = 0 := by
    have hz := lie_mem_genWeightSpace_of_mem_genWeightSpace ha hv
    change ⁅a,⁅a,b⁆⁆ ∈ rootSpace H (α + θ) at hz
    rw [hαθ] at hz
    exact hz
  have hbv : ⁅b,⁅a,b⁆⁆ = 0 := by
    have hz := lie_mem_genWeightSpace_of_mem_genWeightSpace hb hv
    change ⁅b,⁅a,b⁆⁆ ∈ rootSpace H (β + θ) at hz
    rw [hβθ] at hz
    exact hz
  change (θ : H → K) ≠ 0 at hθ
  obtain ⟨h, hh⟩ := Function.ne_iff.mp hθ
  refine ⟨a, b, (h : L), ⁅a,b⁆, θ h, hab, hh, rfl, ?_, hav, hbv⟩
  exact lie_eq_smul_of_mem_rootSpace hv h

/-- Basepoint-free compatible families exclude the displayed root configuration. -/
theorem no_highest_root_configuration
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ B ∈ forms, LieObstruction.Compatible B)
    (hfree : LieObstruction.BasepointFree forms)
    (α β θ : Weight K H L) (hα : α.IsNonZero) (hθ : θ.IsNonZero)
    (hsum : (θ : H → K) = α + β)
    (hαθ : rootSpace H (α + θ) = ⊥) (hβθ : rootSpace H (β + θ) = ⊥) : False := by
  obtain ⟨a,b,h,v,c,hv,hc,hab,hhv,hav,hbv⟩ :=
    exists_highest_witness α β θ hα hθ hsum hαθ hβθ
  exact LieObstruction.no_highest_root_witness forms hcompatible hfree
    a b h v c hv hc hab hhv hav hbv
/-- A nonzero functional absent from the root system has zero root space. -/
theorem rootSpace_eq_bot_of_not_root (χ : Module.Dual K H)
    (hχ : χ ≠ 0) (hnot : χ ∉ Set.range (rootSystem H).root) :
    rootSpace H χ = ⊥ := by
  by_contra hn
  let w : Weight K H L := ⟨χ, hn⟩
  have hw : w.IsNonZero := by
    intro hz
    apply hχ
    exact LinearMap.ext (congrFun hz)
  let i : H.root := ⟨w, by simpa only [LieSubalgebra.root, Finset.mem_filter,
    Finset.mem_univ, true_and] using hw⟩
  apply hnot
  exact ⟨i,rfl⟩

set_option maxHeartbeats 150000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- A simple splitting Killing Lie algebra of rank at least two cannot carry
any basepoint-free family satisfying the paper's compatibility relation. -/
theorem no_high_rank_simple_compatible [LieAlgebra.IsSimple K L]
    (hdim : 2 ≤ Module.finrank K H)
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ B ∈ forms, LieObstruction.Compatible B)
    (hfree : LieObstruction.BasepointFree forms) : False := by
  classical
  have hd : 2 ≤ Module.finrank K (Module.Dual K H) := by simpa using hdim
  have : Nonempty H.root := by
    by_contra hn
    have : IsEmpty H.root := not_nonempty_iff.mp hn
    have ht := RootPairing.IsRootSystem.span_root_eq_top (P := rootSystem H)
    have hr : Set.range (rootSystem H).root = ∅ := by ext x; simp
    rw [hr, Submodule.span_empty] at ht
    have heq := congrArg (fun q : Submodule K (Module.Dual K H) => Module.finrank K q) ht
    simp only [finrank_bot, finrank_top] at heq
    omega
  let : (rootSystem H).IsIrreducible := (isSimple_iff_isIrreducible (K := K) (L := L) (H := H)).2 inferInstance
  obtain ⟨b⟩ := RootPairing.nonempty_base (rootSystem H)
  obtain ⟨θ,α,β,hθ,hα,hβ,hsum,hθα,hθβ⟩ :=
    RootCombinatorics.exists_highest_configuration (rootSystem H) b hd
  have hs : ((θ : Weight K H L) : H → K) =
      (α : Weight K H L) + (β : Weight K H L) := by
    exact congrArg (fun f : Module.Dual K H => (f : H → K)) hsum
  have hneA := RootCombinatorics.positive_sum_ne_zero (rootSystem H) b θ α hθ hα
  have hneB := RootCombinatorics.positive_sum_ne_zero (rootSystem H) b θ β hθ hβ
  have hspaceA : rootSpace H ((α : Weight K H L) + (θ : Weight K H L)) = ⊥ := by
    have h := rootSpace_eq_bot_of_not_root ((rootSystem H).root θ + (rootSystem H).root α) hneA hθα
    simpa only [rootSystem_root_apply, LinearMap.coe_add, Weight.coe_coe, add_comm] using h
  have hspaceB : rootSpace H ((β : Weight K H L) + (θ : Weight K H L)) = ⊥ := by
    have h := rootSpace_eq_bot_of_not_root ((rootSystem H).root θ + (rootSystem H).root β) hneB hθβ
    simpa only [rootSystem_root_apply, LinearMap.coe_add, Weight.coe_coe, add_comm] using h
  exact no_highest_root_configuration (K := K) (L := L) (H := H) forms hcompatible hfree
    (α : Weight K H L) (β : Weight K H L) (θ : Weight K H L)
    (H.isNonZero_coe_root α) (H.isNonZero_coe_root θ) hs hspaceA hspaceB
/-- Compatibility forces the Cartan rank of an actual simple factor to be one. -/
theorem cartan_finrank_eq_one_of_compatible [LieAlgebra.IsSimple K L]
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ B ∈ forms, LieObstruction.Compatible B)
    (hfree : LieObstruction.BasepointFree forms) : Module.finrank K H = 1 := by
  have hle : Module.finrank K H ≤ 1 := by
    by_contra hn
    have hd : 2 ≤ Module.finrank K H := by omega
    exact no_high_rank_simple_compatible (K := K) (L := L) (H := H) hd forms hcompatible hfree
  let : (rootSystem H).IsIrreducible :=
    (isSimple_iff_isIrreducible (K := K) (L := L) (H := H)).2 inferInstance
  have : Nontrivial H := RootPairing.IsIrreducible.nontrivial' (rootSystem H)
  have hp : 0 < Module.finrank K H := Module.finrank_pos
  omega
end NcCubic.RootWitness
