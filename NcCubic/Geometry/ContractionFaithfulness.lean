module
public import NcCubic.Geometry.ContractionEvaluation
public import NcCubic.Geometry.AffineTangent
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
/-- Module sections are determined on affine subopens, without quasicoherence. -/
theorem moduleSection_ext_affine {X : Scheme.{u}} (M : X.Modules) (W : X.Opens)
    (s t : Γ(M,W))
    (h : ∀ V : X.Opens, IsAffineOpen V → ∀ hVW : V ≤ W,
      M.presheaf.map (homOfLE hVW).op s = M.presheaf.map (homOfLE hVW).op t) : s = t := by
  let I := {V : X.Opens // IsAffineOpen V ∧ V ≤ W}
  let C : I → X.Opens := fun V => V.val
  have hc : W ≤ iSup C := by
    intro x hx
    obtain ⟨V,hV,hxV,hVW⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V,hV,hVW⟩,hxV⟩
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf,M.isSheaf⟩
  apply F.eq_of_locally_eq' C W (fun i => homOfLE i.prop.2) hc
  intro i
  exact h i.val i.prop.1 i.prop.2

/-- Local internal-Hom sections are determined on every actual subopen. -/
theorem localHomFamily_ext {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (c d : (restrFun X.sheaf.obj U).obj M.val ⟶ (restrFun X.sheaf.obj U).obj N.val)
    (h : ∀ (V : X.Opens) (hVU : V ≤ U) (a : Γ(M,V)),
      localHomFamily M N U c V hVU a = localHomFamily M N U d V hVU a) : c = d := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change localHomFamily M N U c Z.unop.left (leOfHom Z.unop.hom) a =
    localHomFamily M N U d Z.unop.left (leOfHom Z.unop.hom) a
  exact h _ _ a

/-- The genuine internal Hom of two actual sheaves of modules. -/
def moduleHomSheaf {X : Scheme.{u}} (M N : X.Modules) : X.Modules where
  val := internalHom X.sheaf.obj M.val N.val
  isSheaf := internalHom_isSheaf X.sheaf.obj M.val N.val N.isSheaf

/-- Actual sheaf internal-Hom sections are determined on every subopen. -/
theorem sheafHomSection_ext {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (c d : Γ(moduleHomSheaf M N,U))
    (h : ∀ (V : X.Opens) (hVU : V ≤ U) (a : Γ(M,V)),
      localHomFamily M N U c V hVU a = localHomFamily M N U d V hVU a) : c = d :=
  localHomFamily_ext M N U c d h

theorem moduleSection_restrict_comp {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (f : V ⟶ U) (g : W ⟶ V) (h : W ⟶ U)
    (q : Γ(M,U)) : M.val.map g.op (M.val.map f.op q) = M.val.map h.op q :=
  (M.val.map_comp_apply f.op g.op q).symm.trans
    (PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) q)

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of R))
theorem affine_contractionHamiltonian_ext (U : X.Opens) (hU : IsAffineOpen U)
    (c d : Γ(tangentContractionSheaf f,U))
    (h : ∀ a b, contractionSectionBracket f U c a b = contractionSectionBracket f U d a b)
    (a : Γ(X,U)) : contractionHamiltonian f U c a = contractionHamiltonian f U d a := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  apply (affineTangentDerivationEquiv f U hU).injective
  apply Derivation.ext
  intro b
  exact (congrArg (fun q => q b)
    (affineTangentDerivationEquiv_apply f U hU (contractionHamiltonian f U c a))).trans
      ((h a b).trans (congrArg (fun q => q b)
        (affineTangentDerivationEquiv_apply f U hU (contractionHamiltonian f U d a))).symm)

theorem affine_contractionEvaluation_ext (U : X.Opens) (hU : IsAffineOpen U)
    (c d : Γ(tangentContractionSheaf f,U))
    (h : ∀ a b, contractionSectionBracket f U c a b = contractionSectionBracket f U d a b)
    (α : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    contractionEvaluation f U c α = contractionEvaluation f U d α := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  let e := affineCotangentSectionsEquiv f U hU
  let k := (contractionEvaluation f U c).comp e.symm.toLinearMap
  let l := (contractionEvaluation f U d).comp e.symm.toLinearMap
  have hk (a : Γ(X,U)) : k (KaehlerDifferential.D R Γ(X,U) a) =
      l (KaehlerDifferential.D R Γ(X,U) a) := by
    have hd := congrArg e.symm (affineCotangentSectionsEquiv_d f U hU a)
    have hd' := hd.symm.trans (e.symm_apply_apply _)
    exact (congrArg (contractionEvaluation f U c) hd').trans
      ((affine_contractionHamiltonian_ext f U hU c d h a).trans
        (congrArg (contractionEvaluation f U d) hd').symm)
  have heq : k = l := by
    apply LinearMap.ext
    intro β
    have hβ : β ∈ Submodule.span Γ(X,U) (Set.range (KaehlerDifferential.D R Γ(X,U))) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hβ using Submodule.span_induction with
    | mem x hx => obtain ⟨a,rfl⟩ := hx; exact hk a
    | zero => rw [map_zero,map_zero]
    | add x y _ _ hx hy => rw [map_add,map_add,hx,hy]
    | smul a x _ hx => rw [map_smul,map_smul,hx]
  have ht := LinearMap.congr_fun heq (e α)
  change contractionEvaluation f U c (e.symm (e α)) =
    contractionEvaluation f U d (e.symm (e α)) at ht
  exact (congrArg (contractionEvaluation f U c) (e.symm_apply_apply α)).symm.trans
    (ht.trans (congrArg (contractionEvaluation f U d) (e.symm_apply_apply α)))

theorem contractionEvaluation_ext_local (W : X.Opens)
    (c d : Γ(tangentContractionSheaf f,W))
    (h : ∀ (V : X.Opens) (hVW : V ≤ W) (a b : Γ(X,V)),
      contractionSectionBracket f V ((tangentContractionSheaf f).val.map (homOfLE hVW).op c) a b =
      contractionSectionBracket f V ((tangentContractionSheaf f).val.map (homOfLE hVW).op d) a b)
    (α : Γ(Scheme.Hom.relativeDifferentials f,W)) :
    contractionEvaluation f W c α = contractionEvaluation f W d α := by
  apply moduleSection_ext_affine (tangentSheaf f) W
  intro V hV hVW
  exact (contractionEvaluation_natural f hVW c α).trans
    ((affine_contractionEvaluation_ext f V hV _ _ (h V hVW)
      ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE hVW).op α)).trans
        (contractionEvaluation_natural f hVW d α).symm)

set_option maxHeartbeats 4000000 in
theorem contractionGlobalBracket_bracket (c : Γ(tangentContractionSheaf f,⊤))
    (U : X.Opens) (a b : Γ(X,U)) :
    (contractionGlobalBracket f c).bracket U a b =
    contractionSectionBracket f U
      ((tangentContractionSheaf f).val.map (homOfLE (le_top : U ≤ ⊤)).op c) a b := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
theorem contractionGlobalBracket_ext (c d : Γ(tangentContractionSheaf f,⊤))
    (h : ∀ (U : X.Opens) (a b : Γ(X,U)),
      (contractionGlobalBracket f c).bracket U a b =
      (contractionGlobalBracket f d).bracket U a b) : c = d := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  let W := Z.unop.left
  let hW : W ≤ ⊤ := leOfHom Z.unop.hom
  change contractionEvaluation f W
    ((tangentContractionSheaf f).val.map Z.unop.hom.op c) α =
    contractionEvaluation f W ((tangentContractionSheaf f).val.map Z.unop.hom.op d) α
  apply contractionEvaluation_ext_local f
  intro V hV a b
  have hm : Z.unop.hom.op ≫ (homOfLE hV).op = (homOfLE (le_top : V ≤ ⊤)).op :=
    Subsingleton.elim _ _
  have hc (q : Γ(tangentContractionSheaf f,⊤)) :
      (tangentContractionSheaf f).val.map (homOfLE hV).op
        ((tangentContractionSheaf f).val.map Z.unop.hom.op q) =
        (tangentContractionSheaf f).val.map (homOfLE (le_top : V ≤ ⊤)).op q :=
    moduleSection_restrict_comp (tangentContractionSheaf f) Z.unop.hom
      (homOfLE hV) (homOfLE (le_top : V ≤ ⊤)) q
  rw [hc c, hc d]
  exact ((contractionGlobalBracket_bracket f c V a b).symm.trans (h V a b)).trans
    (contractionGlobalBracket_bracket f d V a b)

theorem contractionGlobalBracket_injective : Function.Injective (contractionGlobalBracket f) := by
  intro c d h
  exact contractionGlobalBracket_ext f c d
    (fun U a b => congrArg (fun B : StructureSheafBracket X => B.bracket U a b) h)
end NcCubic.Geometry
