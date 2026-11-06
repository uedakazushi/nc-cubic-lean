module
public import NcCubic.FactorBasis
public import Mathlib.LinearAlgebra.Basis.Prod
@[expose] public section
noncomputable section
namespace NcCubic.TrivectorBlocks

/-- Extend a factor-adapted basis of the support by its metric-orthogonal
central complement, and reconstruct the ambient trivector. -/
theorem normal_form_of_support_factor_basis {N k : ℕ}
    (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate)
    (hBr : (B.restrict (SupportConstruction.support P)).Nondegenerate)
    (I : Fin k → Submodule ℂ (SupportConstruction.support P))
    (bsU : ∀ s, Module.Basis (Fin 3) ℂ (I s))
    (bU : Module.Basis (Fin k × Fin 3) ℂ (SupportConstruction.support P))
    (hactive : ∀ s j, bU (s, j) = (bsU s j : SupportConstruction.support P))
    (hcomm : ∀ s t, s ≠ t → ∀ (x : I s) (y : I t),
      SupportConstruction.raisedBracket P B (x : SupportConstruction.support P)
        (y : SupportConstruction.support P) = 0)
    (hnonabelian : ∀ s, ∃ x y : I s,
      SupportConstruction.raisedBracket P B (x : SupportConstruction.support P)
        (y : SupportConstruction.support P) ≠ 0) :
    ∃ (m : ℕ) (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)), HasBlockTrivector P b := by
  classical
  let U := SupportConstruction.support P
  let Z := B.orthogonal U
  have hc : IsCompl U Z := B.isCompl_orthogonal_of_restrict_nondegenerate hsym.isRefl hBr
  let bz := Module.finBasis ℂ Z
  let W : Fin k → Submodule ℂ (CoordinateSpace N) := fun s => (I s).map U.subtype
  let E := fun s => Submodule.equivMapOfInjective U.subtype U.injective_subtype (I s)
  let bs := fun s => (bsU s).map (E s)
  let b : Module.Basis (BlockIndex k (Module.finrank ℂ Z)) ℂ (CoordinateSpace N) :=
    (bU.prod bz).map (Submodule.prodEquivOfIsCompl U Z hc)
  obtain ⟨b', hb'⟩ := normal_form_of_adapted_commuting_subspaces P B hsym hB W Z b bs bz
    (by
      intro s j
      simp [b, bs, E, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl', hactive])
    (by
      intro j
      simp [b, Module.Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl'])
    (by
      intro z y
      exact (SupportConstruction.central_iff_orthogonal_support P B hsym hB z).mpr z.property y)
    (by
      intro s t hst x y
      have hh := hcomm s t hst ((E s).symm x) ((E t).symm y)
      have hx := Submodule.map_equivMapOfInjective_symm_apply U.subtype U.injective_subtype (I s) x
      have hy := Submodule.map_equivMapOfInjective_symm_apply U.subtype U.injective_subtype (I t) y
      change SupportConstruction.raisedBracket P B
        (U.subtype ((E s).symm x)) (U.subtype ((E t).symm y)) = 0 at hh
      rw [hx, hy] at hh
      exact hh)
    (by
      intro s
      obtain ⟨x, y, hxy⟩ := hnonabelian s
      refine ⟨E s x, E s y, ?_⟩
      change SupportConstruction.raisedBracket P B (x : U) (y : U) ≠ 0
      exact hxy)
  exact ⟨Module.finrank ℂ Z, b', hb'⟩

end NcCubic.TrivectorBlocks
