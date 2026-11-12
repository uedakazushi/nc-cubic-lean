module
public import NcCubic.Geometry.ExteriorDualStalk
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
/-- Finitely many module germs admit representatives on one common neighborhood. -/
theorem exists_germ_family {X : Scheme.{u}} (M : X.Modules) (x : X)
    {I : Type u} [Finite I] (s : I → M.presheaf.stalk x) :
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
end NcCubic.Geometry
