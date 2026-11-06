module
public import NcCubic.FactorCoordinates
public import Mathlib.Algebra.DirectSum.Module
@[expose] public section
noncomputable section
namespace NcCubic.TrivectorBlocks

/-- Index conversion from a disjoint union of factor bases to the target index. -/
def internalBlockIndexEquiv (k m : ℕ) :
    (Σ i : Fin k ⊕ PUnit, Sum.elim (fun _ : Fin k => Fin 3) (fun _ : PUnit => Fin m) i) ≃
      BlockIndex k m where
  toFun x := by
    rcases x with ⟨i, j⟩
    cases i with
    | inl s => exact Sum.inl (s, j)
    | inr u => exact Sum.inr j
  invFun x := by
    cases x with
    | inl si => exact ⟨Sum.inl si.1, si.2⟩
    | inr j => exact ⟨Sum.inr PUnit.unit, j⟩
  left_inv := by
    rintro ⟨(s | u), j⟩
    · rfl
    · cases u; rfl
  right_inv := by rintro (⟨s, i⟩ | j) <;> rfl

/-- Collect three-dimensional factor bases and a central complement basis. -/
def internalBlockBasis {N k m : ℕ}
    (W : Fin k → Submodule ℂ (CoordinateSpace N)) (Z : Submodule ℂ (CoordinateSpace N))
    (h : DirectSum.IsInternal (Sum.elim W (fun _ : PUnit => Z)))
    (bs : ∀ s, Module.Basis (Fin 3) ℂ (W s)) (bz : Module.Basis (Fin m) ℂ Z) :
    Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N) :=
  (h.collectedBasis (fun i => by cases i with
    | inl s => exact bs s
    | inr u => exact bz)).reindex (internalBlockIndexEquiv k m)

@[simp] theorem internalBlockBasis_active {N k m : ℕ}
    (W : Fin k → Submodule ℂ (CoordinateSpace N)) (Z : Submodule ℂ (CoordinateSpace N))
    (h : DirectSum.IsInternal (Sum.elim W (fun _ : PUnit => Z)))
    (bs : ∀ s, Module.Basis (Fin 3) ℂ (W s)) (bz : Module.Basis (Fin m) ℂ Z)
    (s : Fin k) (j : Fin 3) :
    internalBlockBasis W Z h bs bz (Sum.inl (s, j)) = (bs s j : CoordinateSpace N) := by
  simp [internalBlockBasis, internalBlockIndexEquiv]
  rfl

@[simp] theorem internalBlockBasis_center {N k m : ℕ}
    (W : Fin k → Submodule ℂ (CoordinateSpace N)) (Z : Submodule ℂ (CoordinateSpace N))
    (h : DirectSum.IsInternal (Sum.elim W (fun _ : PUnit => Z)))
    (bs : ∀ s, Module.Basis (Fin 3) ℂ (W s)) (bz : Module.Basis (Fin m) ℂ Z) (j : Fin m) :
    internalBlockBasis W Z h bs bz (Sum.inr j) = (bz j : CoordinateSpace N) := by
  simp [internalBlockBasis, internalBlockIndexEquiv]
  rfl

/-- An internal direct sum of commuting nonabelian three-dimensional factors
and a central complement gives the normalized trivector block form. The tensor
equality is proved from the Cartan form; it is not a premise. -/
theorem normal_form_of_internal_commuting_factors {N k m : ℕ}
    (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate)
    (W : Fin k → Submodule ℂ (CoordinateSpace N)) (Z : Submodule ℂ (CoordinateSpace N))
    (h : DirectSum.IsInternal (Sum.elim W (fun _ : PUnit => Z)))
    (bs : ∀ s, Module.Basis (Fin 3) ℂ (W s)) (bz : Module.Basis (Fin m) ℂ Z)
    (hcenter : ∀ (z : Z) (y : CoordinateSpace N), SupportConstruction.raisedBracket P B z y = 0)
    (hcomm : ∀ s t, s ≠ t → ∀ (x : W s) (y : W t),
      SupportConstruction.raisedBracket P B x y = 0)
    (hnonabelian : ∀ s, ∃ x y : W s, SupportConstruction.raisedBracket P B x y ≠ 0) :
    ∃ b' : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N), HasBlockTrivector P b' := by
  classical
  let b := internalBlockBasis W Z h bs bz
  let C := SupportConstruction.raisedBracket P B
  apply normal_form_of_commuting_basis P B hsym hB b
  · intro j y
    simpa only [b, internalBlockBasis_center] using hcenter (bz j) y
  · intro s t hst i j
    simpa only [b, internalBlockBasis_active] using hcomm s t hst (bs s i) (bs t j)
  · intro s hz
    let v : Fin k → Fin 3 → CoordinateSpace N := fun t j => b (Sum.inl (t, j))
    have hv (x : W s) : factorInclusion v s ((bs s).repr x) = (x : CoordinateSpace N) := by
      rw [factorInclusion_apply]
      have he := congrArg (fun y : W s => (y : CoordinateSpace N)) ((bs s).sum_repr x)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, v, b, internalBlockBasis_active] using he
    have hlocal (x y z : W s) : B (C x y) z = 0 := by
      have he := congrArg (fun Q : AlternatingMap ℂ (CoordinateSpace 3) ℂ (Fin 3) =>
        Q ![(bs s).repr x, (bs s).repr y, (bs s).repr z]) hz
      simp only [factorThreeForm, AlternatingMap.compLinearMap_apply, zero_apply] at he
      have ht : (fun i : Fin 3 => B (factorInclusion v s
          (![⇑((bs s).repr x), ⇑((bs s).repr y), ⇑((bs s).repr z)] i))) =
          ![B (factorInclusion v s ((bs s).repr x)),
            B (factorInclusion v s ((bs s).repr y)),
            B (factorInclusion v s ((bs s).repr z))] := by
        funext i
        fin_cases i <;> rfl
      change P (fun i : Fin 3 => B (factorInclusion v s
        (![⇑((bs s).repr x), ⇑((bs s).repr y), ⇑((bs s).repr z)] i))) = 0 at he
      rw [ht] at he
      rw [hv, hv, hv] at he
      exact (SupportConstruction.pair_raisedBracket P B hsym x y z).trans he
    obtain ⟨x, y, hxy⟩ := hnonabelian s
    apply hxy
    apply hB.1
    have hf : B (C x y) = 0 := by
      apply b.ext
      intro i
      change B (C x y) (b i) = 0
      cases i with
      | inl ti =>
        obtain ⟨t, j⟩ := ti
        change B (C x y) (internalBlockBasis W Z h bs bz (Sum.inl (t, j))) = 0
        rw [internalBlockBasis_active]
        by_cases hst : s = t
        · subst t
          exact hlocal x y (bs s j)
        · rw [SupportConstruction.raisedBracket_invariant P B hsym,
            hcomm s t hst y (bs t j)]
          simp
      | inr j =>
        change B (C x y) (internalBlockBasis W Z h bs bz (Sum.inr j)) = 0
        rw [internalBlockBasis_center, SupportConstruction.raisedBracket_invariant P B hsym,
          SupportLie.skew_of_alternating C (SupportConstruction.raisedBracket_self P B)
            y (bz j), hcenter]
        simp
    intro z
    exact congrArg (fun f : Covector N => f z) hf

/-- A basis adapted to commuting subspaces, without requiring the subspaces
as ambient Lie ideals, suffices for reconstruction. This permits factors inside
an intrinsic support algebra to be mapped to the ambient vector space. -/
theorem normal_form_of_adapted_commuting_subspaces {N k m : ℕ}
    (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate)
    (W : Fin k → Submodule ℂ (CoordinateSpace N)) (Z : Submodule ℂ (CoordinateSpace N))
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (bs : ∀ s, Module.Basis (Fin 3) ℂ (W s)) (bz : Module.Basis (Fin m) ℂ Z)
    (hactive : ∀ s j, b (Sum.inl (s, j)) = (bs s j : CoordinateSpace N))
    (hcentralbasis : ∀ j, b (Sum.inr j) = (bz j : CoordinateSpace N))
    (hcenter : ∀ (z : Z) (y : CoordinateSpace N), SupportConstruction.raisedBracket P B z y = 0)
    (hcomm : ∀ s t, s ≠ t → ∀ (x : W s) (y : W t),
      SupportConstruction.raisedBracket P B x y = 0)
    (hnonabelian : ∀ s, ∃ x y : W s, SupportConstruction.raisedBracket P B x y ≠ 0) :
    ∃ b' : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N), HasBlockTrivector P b' := by
  classical
  let C := SupportConstruction.raisedBracket P B
  apply normal_form_of_commuting_basis P B hsym hB b
  · intro j y
    simpa only [hcentralbasis] using hcenter (bz j) y
  · intro s t hst i j
    simpa only [hactive] using hcomm s t hst (bs s i) (bs t j)
  · intro s hz
    let v : Fin k → Fin 3 → CoordinateSpace N := fun t j => b (Sum.inl (t, j))
    have hv (x : W s) : factorInclusion v s ((bs s).repr x) = (x : CoordinateSpace N) := by
      rw [factorInclusion_apply]
      have he := congrArg (fun y : W s => (y : CoordinateSpace N)) ((bs s).sum_repr x)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, v, hactive] using he
    have hlocal (x y z : W s) : B (C x y) z = 0 := by
      have he := congrArg (fun Q : AlternatingMap ℂ (CoordinateSpace 3) ℂ (Fin 3) =>
        Q ![(bs s).repr x, (bs s).repr y, (bs s).repr z]) hz
      simp only [factorThreeForm, AlternatingMap.compLinearMap_apply, zero_apply] at he
      have ht : (fun i : Fin 3 => B (factorInclusion v s
          (![⇑((bs s).repr x), ⇑((bs s).repr y), ⇑((bs s).repr z)] i))) =
          ![B (factorInclusion v s ((bs s).repr x)),
            B (factorInclusion v s ((bs s).repr y)),
            B (factorInclusion v s ((bs s).repr z))] := by
        funext i
        fin_cases i <;> rfl
      change P (fun i : Fin 3 => B (factorInclusion v s
        (![⇑((bs s).repr x), ⇑((bs s).repr y), ⇑((bs s).repr z)] i))) = 0 at he
      rw [ht] at he
      rw [hv, hv, hv] at he
      exact (SupportConstruction.pair_raisedBracket P B hsym x y z).trans he
    obtain ⟨x, y, hxy⟩ := hnonabelian s
    apply hxy
    apply hB.1
    have hf : B (C x y) = 0 := by
      apply b.ext
      intro i
      change B (C x y) (b i) = 0
      cases i with
      | inl ti =>
        obtain ⟨t, j⟩ := ti
        rw [hactive]
        by_cases hst : s = t
        · subst t
          exact hlocal x y (bs s j)
        · rw [SupportConstruction.raisedBracket_invariant P B hsym,
            hcomm s t hst y (bs t j)]
          simp
      | inr j =>
        rw [hcentralbasis, SupportConstruction.raisedBracket_invariant P B hsym,
          SupportLie.skew_of_alternating C (SupportConstruction.raisedBracket_self P B)
            y (bz j), hcenter]
        simp
    intro z
    exact congrArg (fun f : Covector N => f z) hf

end NcCubic.TrivectorBlocks
