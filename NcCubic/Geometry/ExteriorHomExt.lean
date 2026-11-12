/- Canonical exterior/tensor comparison on actual local sections. -/
module
public import NcCubic.Geometry.ImmersionBracketNaturality
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.PresheafOfModules.InternalHom
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
private lemma adjunction_unit_transport_inj
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {Z : C} {A G : D} (e : A ≅ L.obj Z) (f g : A ⟶ G)
    (h : adj.unit.app Z ≫ R.map e.inv ≫ R.map f =
      adj.unit.app Z ≫ R.map e.inv ≫ R.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  apply (adj.homEquiv Z G).injective
  rw [adj.homEquiv_unit,adj.homEquiv_unit]
  simpa only [Functor.map_comp,Category.assoc] using h

set_option backward.isDefEq.respectTransparency false in
lemma exterior_hom_ext_on_wedges {X : Scheme.{u}} (M N : X.Modules)
    (f g : Scheme.Modules.exteriorPower M (2:ℤ) ⟶ N)
    (h : ∀ (U : X.Opens) (v : Fin 2 → Γ(M,U)),
      f.val.app (op U) (exteriorWedgeAlternating M U v) =
      g.val.app (op U) (exteriorWedgeAlternating M U v)) : f = g := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 X.sheaf.obj))
  let e := SheafOfModules.exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X)
    (SheafOfModules.algebras _ M) 2
  apply adjunction_unit_transport_inj adj e f g
  change exteriorPresheafUnit M ≫ (moduleUnderlyingFunctor X).map f =
    exteriorPresheafUnit M ≫ (moduleUnderlyingFunctor X).map g
  apply exteriorRawHom_ext _ _ 2
  intro U v
  have hu := h U.unop (fun i => siteSectionSemilinearEquiv M U.unop (v i))
  rw [exteriorWedgeAlternating_raw] at hu
  exact hu
lemma tensorHomEquiv_over_eval (X : RingedSpace.{u,u})
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X))
    (t : ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj F).obj G ⟶ H)
    (U : TopologicalSpace.Opens X.carrier) (a : F.val.obj (op U)) (Z : Over U)
    (b : G.val.obj (op Z.left)) :
    (((SheafTensorCurry.tensorHomEquiv X F G H t).val.app (op U) a).app (op Z)).hom b =
      t.val.app (op Z.left)
        (toTensorSheafSection X F G (op Z.left)
          (F.val.map Z.hom.op a ⊗ₜ[X.presheaf.obj (op Z.left)] b)) := by
  have h := presheafTensorHomEquiv_apply X.presheaf F.val G.val H.val
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t) U a Z.hom b
  change (((SheafTensorCurry.tensorHomEquiv X F G H t).val.app (op U) a).app (op Z)).hom b =
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t).app (op Z.left)
      (F.val.map Z.hom.op a ⊗ₜ[X.presheaf.obj (op Z.left)] b) at h
  have hb := (PresheafOfModules.sheafificationAdjunction
    (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).homEquiv_unit
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) H t
  change PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t =
    sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) ≫ t.val at hb
  rwa [hb] at h
set_option backward.isDefEq.respectTransparency false in
lemma exterior_internalHom_ext_on_wedges {X : Scheme.{u}} (M H : X.Modules) (U : X.Opens)
    (lam mu : Γ(SheafTensorCurry.sheafHomSpace X.toRingedSpace
      (Scheme.Modules.exteriorPower M (2:ℤ)) H,U))
    (h : ∀ (Z : Over U) (v : Fin 2 → Γ(M,Z.left)),
      (lam.app (op Z)).hom (exteriorWedgeAlternating M Z.left v) =
      (mu.app (op Z)).hom (exteriorWedgeAlternating M Z.left v)) : lam = mu := by
  letI : PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology ↥X).over U)
      (restrictedExteriorUnit M U) := restrictedExteriorUnit_locallySurjective M U
  letI : PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology ↥X).over U)
      (restrictedExteriorUnit M U) := restrictedExteriorUnit_locallyInjective M U
  let e := PresheafOfModules.homEquivOfIsLocallyBijective
    (restrictedExteriorUnit M U) (SliceModule H U).isSheaf
  apply e.injective
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  let F := SheafOfModules.valPresheaf (Osharp := X.sheaf)
    (Opens.grothendieckTopology ↥X) M
  let eF := PresheafOfModules.extPowSections 2 F (op Z.unop.left)
  let a := ((e lam).app Z).hom
  let b := ((e mu).app Z).hom
  have hh : a.comp eF.symm.toLinearMap = b.comp eF.symm.toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hz := h Z.unop (fun j => siteSectionSemilinearEquiv M Z.unop.left (v j))
    rw [exteriorWedgeAlternating_raw] at hz
    exact hz
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun hh (eF z)
  exact (congrArg a (eF.symm_apply_apply z)).symm.trans
    (hz.trans (congrArg b (eF.symm_apply_apply z)))

set_option backward.isDefEq.respectTransparency false in
lemma tensor_exterior_pairing_ext {X : Scheme.{u}} (M N H : X.Modules)
    (f g : ((Tensor.sheafTensor X.sheaf).obj (Scheme.Modules.exteriorPower M (2:ℤ))).obj
      (Scheme.Modules.exteriorPower N (2:ℤ)) ⟶ H)
    (h : ∀ (U : X.Opens) (v : Fin 2 → Γ(M,U)) (w : Fin 2 → Γ(N,U)),
      f.val.app (op U) (PullbackDual.tensorSheafPure X _ _ U
        (exteriorWedgeAlternating M U v ⊗ₜ[X.presheaf.obj (op U)] exteriorWedgeAlternating N U w)) =
      g.val.app (op U) (PullbackDual.tensorSheafPure X _ _ U
        (exteriorWedgeAlternating M U v ⊗ₜ[X.presheaf.obj (op U)] exteriorWedgeAlternating N U w))) : f = g := by
  apply (SheafTensorCurry.tensorHomEquiv X.toRingedSpace _ _ _).injective
  apply exterior_hom_ext_on_wedges M (SheafTensorCurry.sheafHomSpace X.toRingedSpace
    (Scheme.Modules.exteriorPower N (2:ℤ)) H)
  intro U v
  apply exterior_internalHom_ext_on_wedges N H U
  intro Z w
  have hf := tensorHomEquiv_over_eval X.toRingedSpace _ _ _ f U
    (exteriorWedgeAlternating M U v) Z (exteriorWedgeAlternating N Z.left w)
  have hg := tensorHomEquiv_over_eval X.toRingedSpace _ _ _ g U
    (exteriorWedgeAlternating M U v) Z (exteriorWedgeAlternating N Z.left w)
  have hw := exteriorWedgeAlternating_natural M Z.hom v
  have hf' := congrArg (fun x => f.val.app (op Z.left)
    (PullbackDual.tensorSheafPure X _ _ Z.left
      (x ⊗ₜ[X.presheaf.obj (op Z.left)] exteriorWedgeAlternating N Z.left w))) hw
  have hg' := congrArg (fun x => g.val.app (op Z.left)
    (PullbackDual.tensorSheafPure X _ _ Z.left
      (x ⊗ₜ[X.presheaf.obj (op Z.left)] exteriorWedgeAlternating N Z.left w))) hw
  exact hf.trans (hf'.trans ((h Z.left (fun j => M.presheaf.map Z.hom.op (v j)) w).trans
    (hg'.symm.trans hg.symm)))
lemma pullback_tensor_exterior_pairing_ext {X P : Scheme.{u}} (i : X ⟶ P)
    (M N : P.Modules) (H : X.Modules)
    (f g : ((Tensor.sheafTensor X.sheaf).obj
      ((Scheme.Modules.pullback i).obj (Scheme.Modules.exteriorPower M (2:ℤ)))).obj
      ((Scheme.Modules.pullback i).obj (Scheme.Modules.exteriorPower N (2:ℤ))) ⟶ H)
    (h : ∀ (U : P.Opens) (v : Fin 2 → Γ(M,U)) (w : Fin 2 → Γ(N,U)),
      f.val.app (op (i ⁻¹ᵁ U)) (PullbackDual.tensorSheafPure X _ _ (i ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Modules.exteriorPower M (2:ℤ))).val.app (op U) (exteriorWedgeAlternating M U v))
          ⊗ₜ[X.presheaf.obj (op (i ⁻¹ᵁ U))]
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Modules.exteriorPower N (2:ℤ))).val.app (op U) (exteriorWedgeAlternating N U w)))) =
      g.val.app (op (i ⁻¹ᵁ U)) (PullbackDual.tensorSheafPure X _ _ (i ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Modules.exteriorPower M (2:ℤ))).val.app (op U) (exteriorWedgeAlternating M U v))
          ⊗ₜ[X.presheaf.obj (op (i ⁻¹ᵁ U))]
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Modules.exteriorPower N (2:ℤ))).val.app (op U) (exteriorWedgeAlternating N U w))))) : f = g := by
  let A := Scheme.Modules.exteriorPower M (2:ℤ)
  let B := Scheme.Modules.exteriorPower N (2:ℤ)
  let e := PullbackDual.pullbackTensorIso i A B
  apply (Iso.homCongr e (Iso.refl H)).symm.injective
  apply ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ H).injective
  apply tensor_exterior_pairing_ext M N ((Scheme.Modules.pushforward i).obj H)
  intro U v w
  let a := exteriorWedgeAlternating M U v
  let b := exteriorWedgeAlternating N U w
  change f.val.app (op (i ⁻¹ᵁ U)) (e.hom.val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _).val.app (op U)
        (PullbackDual.tensorSheafPure P A B U (a ⊗ₜ[P.presheaf.obj (op U)] b)))) =
    g.val.app (op (i ⁻¹ᵁ U)) (e.hom.val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _).val.app (op U)
        (PullbackDual.tensorSheafPure P A B U (a ⊗ₜ[P.presheaf.obj (op U)] b))))
  have ht := PullbackDual.comparison_tensorSheafPure i A B U a b
  exact (congrArg (f.val.app (op (i ⁻¹ᵁ U))) ht).trans
    ((h U v w).trans (congrArg (g.val.app (op (i ⁻¹ᵁ U))) ht).symm)
end NcCubic.Geometry.ImmersionBracketNaturality
