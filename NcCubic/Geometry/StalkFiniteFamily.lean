module
public import NcCubic.Geometry.ExteriorDualStalk
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
/-- Finitely many module germs admit representatives on one common neighborhood. -/
theorem exists_germ_family {X : Scheme.{u}} (M : X.Modules) (x : X)
    {I : Type*} [Finite I] (s : I → M.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (t : I → Γ(M,U)),
      ∀ i, TopCat.Presheaf.germ M.presheaf U x hx (t i) = s i := by
  classical
  let := Fintype.ofFinite I
  choose U hU t ht using fun i => M.presheaf.exists_germ_eq (s i)
  have hW : x ∈ (⨅ i, U i : X.Opens) := by
    have h : x ∈ (↑(⨅ i, U i) : Set X) := by
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.2 hU
    exact h
  refine ⟨⨅ i, U i, hW, fun i => M.presheaf.map (homOfLE (iInf_le U i)).op (t i), ?_⟩
  intro i
  exact (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (iInf_le U i)) x hW (t i)).trans (ht i)
/-- Finite germ representatives may be chosen inside any prescribed neighborhood. -/
theorem exists_germ_family_le {X : Scheme.{u}} (M : X.Modules) (x : X)
    (U₀ : X.Opens) (hx₀ : x ∈ U₀) {I : Type*} [Finite I] (s : I → M.presheaf.stalk x) :
    ∃ (U : X.Opens) (_hU : U ≤ U₀) (hx : x ∈ U) (t : I → Γ(M,U)),
      ∀ i, TopCat.Presheaf.germ M.presheaf U x hx (t i) = s i := by
  classical
  let := Fintype.ofFinite I
  choose U hle hU t ht using fun i => M.presheaf.exists_le_germ_eq (s i) hx₀
  have hxW : x ∈ (⨅ i, U i : X.Opens) := by
    have h : x ∈ (↑(⨅ i, U i) : Set X) := by
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.2 hU
    exact h
  have hx : x ∈ (U₀ ⊓ ⨅ i, U i : X.Opens) := ⟨hx₀, hxW⟩
  let hi (i : I) : U₀ ⊓ ⨅ i, U i ≤ U i := le_trans inf_le_right (iInf_le U i)
  refine ⟨U₀ ⊓ ⨅ i, U i, inf_le_left, hx,
    fun i => M.presheaf.map (homOfLE (hi i)).op (t i), ?_⟩
  intro i
  exact (TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (hi i)) x hx (t i)).trans (ht i)

end NcCubic.Geometry
