module
public import Mathlib.Algebra.Lie.Weights.IsSimple
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
/-!
# Rank-one Killing Lie algebras have dimension three

Relative to a splitting Cartan subalgebra of dimension one, reducedness makes
all roots equal up to sign. The Cartan subalgebra and the two one-dimensional
root spaces give an independent decomposition of the full Lie algebra.
No classification theorem or dimensional conclusion is assumed.
-/

@[expose] public section
noncomputable section
namespace NcCubic.RankOneDimension
open LieModule LieAlgebra LieAlgebra.IsKilling Module
variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

theorem root_eq_or_eq_neg (hH : finrank K H = 1) (α β : H.root) :
    (α : Weight K H L) = β ∨ (α : Weight K H L) = -(β : Weight K H L) := by
  have hli : ¬ LinearIndependent K ![(rootSystem H).root α, (rootSystem H).root β] := by
    intro hi
    have hc := hi.fintype_card_le_finrank
    simp only [Fintype.card_fin, Subspace.dual_finrank_eq, hH] at hc
    omega
  have h := RootPairing.IsReduced.eq_or_eq_neg (P := rootSystem H) α β hli
  rcases h with h | h
  · left
    ext x
    exact congrArg (fun f : Module.Dual K H => f x) h
  · right
    ext x
    exact congrArg (fun f : Module.Dual K H => f x) h


theorem root_nonempty (hH : finrank K H = 1) : Nonempty H.root := by
  classical
  by_contra hn
  let : IsEmpty H.root := not_nonempty_iff.mp hn
  have hs := RootPairing.IsRootSystem.span_root_eq_top (P := rootSystem H)
  have hr : Set.range (rootSystem H).root = ∅ := by ext x; simp
  rw [hr, Submodule.span_empty] at hs
  have hf := congrArg (fun U : Submodule K (Module.Dual K H) => finrank K U) hs
  simp [Subspace.dual_finrank_eq, hH] at hf

theorem top_eq_three_spaces (hH : finrank K H = 1) (α : H.root) :
    (⊤ : LieSubmodule K H L) = H.toLieSubmodule ⊔
      (rootSpace H (α : Weight K H L) ⊔ rootSpace H (-(α : Weight K H L))) := by
  have htop := lieIdeal_eq_inf_cartan_sup_biSup_rootSpace (H := H) (⊤ : LieIdeal K L)
  have hroot : (⨆ β : H.root, rootSpace H (β : Weight K H L)) =
      rootSpace H (α : Weight K H L) ⊔ rootSpace H (-(α : Weight K H L)) := by
    apply le_antisymm
    · apply iSup_le
      intro β
      rcases root_eq_or_eq_neg H hH β α with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    · apply sup_le
      · exact le_iSup (fun β : H.root => rootSpace H (β : Weight K H L)) α
      · have ha : (- (α : Weight K H L)).IsNonZero := (H.isNonZero_coe_root α).neg
        let β : H.root := ⟨-(α : Weight K H L), by simpa [LieSubalgebra.root] using ha⟩
        exact le_iSup (fun β : H.root => rootSpace H (β : Weight K H L)) β
  have hre : LieSubmodule.restr (⊤ : LieSubmodule K L L) H = ⊤ := rfl
  simpa only [hre, top_inf_eq, le_top, iSup_true, hroot] using htop

theorem finrank_eq_three_of_rank_one (hH : finrank K H = 1) : finrank K L = 3 := by
  classical
  obtain ⟨α⟩ := root_nonempty H hH
  have ha0 : (α : H → K) ≠ 0 := H.isNonZero_coe_root α
  have hneg0 : (-(α : H → K)) ≠ 0 := neg_ne_zero.mpr ha0
  have haneg : (α : H → K) ≠ -(α : H → K) := by
    intro h
    have hc := congrFun h (coroot (α : Weight K H L))
    norm_num [root_apply_coroot (H.isNonZero_coe_root α)] at hc
  let A : Submodule K L := (rootSpace H (α : H → K)).toSubmodule
  let B : Submodule K L := (rootSpace H (-(α : H → K))).toSubmodule
  let C : Submodule K L := H.toLieSubmodule.toSubmodule
  have hA : finrank K A = 1 := finrank_rootSpace_eq_one _ (H.isNonZero_coe_root α)
  have hB : finrank K B = 1 := finrank_rootSpace_eq_one (-(α : Weight K H L))
    (H.isNonZero_coe_root α).neg
  have hC : finrank K C = 1 := hH
  have hdAB : Disjoint A B :=
    LieSubmodule.disjoint_toSubmodule.mpr (disjoint_genWeightSpace K H L haneg)
  have hdC : Disjoint C (A ⊔ B) := by
    have hd := iSupIndep_genWeightSpace K H L (0 : H → K)
    have hle : rootSpace H (α : H → K) ⊔ rootSpace H (-(α : H → K)) ≤
        ⨆ (χ : H → K) (_ : χ ≠ 0), rootSpace H χ := by
      exact sup_le (le_iSup₂_of_le (α : H → K) ha0 le_rfl)
        (le_iSup₂_of_le (-(α : H → K)) hneg0 le_rfl)
    have hh := hd.mono_right hle
    change Disjoint (rootSpace H 0) (rootSpace H (α : H → K) ⊔ rootSpace H (-(α : H → K))) at hh
    rw [rootSpace_zero_eq K L H] at hh
    exact LieSubmodule.disjoint_toSubmodule.mpr hh
  have ht : (⊤ : Submodule K L) = C ⊔ (A ⊔ B) := by
    exact congrArg LieSubmodule.toSubmodule (top_eq_three_spaces H hH α)
  have hdimAB := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hdAB.eq_bot, finrank_bot, add_zero, hA, hB] at hdimAB
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq C (A ⊔ B)
  rw [hdC.eq_bot, finrank_bot, add_zero, ← ht, finrank_top, hC, hdimAB] at hdim
  exact hdim
end NcCubic.RankOneDimension
