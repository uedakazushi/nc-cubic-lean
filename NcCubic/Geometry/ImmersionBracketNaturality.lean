/- Actual local cotangent/tangent pullback compatibility and bracket functionals.
These are canonical compatibility lemmas, not an assumed bivector representation. -/
module
public import NcCubic.Geometry.ImmersionBivector
public import NcCubic.Geometry.BivectorEvaluation
public import NcCubic.Geometry.ExteriorRawDualIso
public import NcCubic.Geometry.RawExteriorWedge
public import NcCubic.Geometry.ExteriorWedgeLaws
public import NcCubic.Geometry.BivectorLinearity
public import NcCubic.Geometry.LocalHomFamily
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
open ImmersionBivector
variable {X P S : Scheme.{u}}
lemma cotangentMap_unit_differentials (i : X ⟶ P) (p : P ⟶ S)
    (U : P.Opens) (a : Γ(P,U)) :
    (cotangentMap i p).val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (Scheme.Hom.relativeDifferentials p)).val.app (op U)
          ((Scheme.Hom.universalRelativeDerivation p).d a)) =
      (Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U).hom a) := by
  exact cotangentMap_on_differentials i p U a

lemma tangentMap_differential_pairing (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (U : P.Opens)
    (v : Γ(dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p)),i ⁻¹ᵁ U))
    (a : Γ(P,U)) :
    dualPairing ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p))
      ((ambientDualPullbackIso i p hΩ).hom.val.app (op (i ⁻¹ᵁ U))
        ((tangentMap i p hΩ).val.app (op (i ⁻¹ᵁ U)) v)) (Over.mk (𝟙 (i ⁻¹ᵁ U)))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (Scheme.Hom.relativeDifferentials p)).val.app (op U)
          ((Scheme.Hom.universalRelativeDerivation p).d a)) =
    dualPairing (Scheme.Hom.relativeDifferentials (i ≫ p)) v
      (Over.mk (𝟙 (i ⁻¹ᵁ U)))
      ((Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U).hom a)) := by
  exact (tangentMap_pairing i p hΩ (i ⁻¹ᵁ U) v (Over.mk (𝟙 (i ⁻¹ᵁ U))) _).trans
    (congrArg (dualPairing (Scheme.Hom.relativeDifferentials (i ≫ p)) v
      (Over.mk (𝟙 (i ⁻¹ᵁ U)))) (cotangentMap_unit_differentials i p U a))
lemma tangent_derivation_of_extension (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) (U : P.Opens)
    (v : Γ(tangentSheaf (i ≫ p),i ⁻¹ᵁ U)) (w : Γ(tangentSheaf p,U))
    (h : (tangentMap i p hΩ).val.app (op (i ⁻¹ᵁ U)) v =
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (tangentSheaf p)).val.app (op U) w))
    (a : Γ(P,U)) :
    tangentSectionDerivation (i ≫ p) (i ⁻¹ᵁ U) v ((i.app U).hom a) =
      (i.app U).hom (tangentSectionDerivation p U w a) := by
  have ht := tangentMap_differential_pairing i p hΩ U v a
  rw [h] at ht
  exact ht.symm.trans ((PullbackDual.pullbackDualMap_eval i
    (Scheme.Hom.relativeDifferentials p) (i ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (tangentSheaf p)).val.app (op U) w)
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (Scheme.Hom.relativeDifferentials p)).val.app (op U)
        ((Scheme.Hom.universalRelativeDerivation p).d a))).trans
    (PullbackDual.pullbackEvaluation_unit_tmul i (Scheme.Hom.relativeDifferentials p) U w
      ((Scheme.Hom.universalRelativeDerivation p).d a)))
/-- Actual dual base-change is compatible with any genuine local extension
through the transpose of a specified module morphism. -/
lemma dualPairing_pullback_of_extension (i : X ⟶ P) (M : P.Modules) (N : X.Modules)
    (c : (Scheme.Modules.pullback i).obj M ⟶ N) (U : P.Opens)
    (lamP : Γ(dualSheaf M,U)) (lamX : Γ(dualSheaf N,i ⁻¹ᵁ U))
    (h : (PullbackDual.pullbackDualMap i M).val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (dualSheaf M)).val.app (op U) lamP) =
      (dualMap c).val.app (op (i ⁻¹ᵁ U)) lamX)
    (z : Γ(M,U)) :
    (i.app U).hom (dualPairing M lamP (Over.mk (𝟙 U)) z) =
      dualPairing N lamX (Over.mk (𝟙 (i ⁻¹ᵁ U)))
        (c.val.app (op (i ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U) z)) := by
  have he := (PullbackDual.pullbackDualMap_eval i M (i ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (dualSheaf M)).val.app (op U) lamP)
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U) z)).trans
    (PullbackDual.pullbackEvaluation_unit_tmul i M U lamP z)
  rw [h] at he
  exact he.symm.trans (dualPairing_dualMap c lamX (Over.mk (𝟙 (i ⁻¹ᵁ U))) _)
lemma exteriorRawHom_ext {C : Type*} [Category C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}
    (F G : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)) (n : ℕ)
    (a b : PresheafOfModules.extPow (O := O) n F ⟶ G)
    (h : ∀ (U : Cᵒᵖ) (v : Fin n → F.obj U),
      a.app U (PresheafExterior.wedgeSection F n U v) =
      b.app U (PresheafExterior.wedgeSection F n U v)) : a = b := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  let e := PresheafOfModules.extPowSections n F U
  have hh : (a.app U).hom.comp e.symm.toLinearMap =
      (b.app U).hom.comp e.symm.toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    exact h U v
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun hh (e z)
  exact (congrArg (a.app U) (e.symm_apply_apply z)).symm.trans
    (hz.trans (congrArg (b.app U) (e.symm_apply_apply z)))
set_option backward.isDefEq.respectTransparency false in
lemma exteriorDual_ext_on_wedges {Y : Scheme.{u}} (M : Y.Modules) (U : Y.Opens)
    (lam mu : Γ(dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)),U))
    (h : ∀ (Z : Over U) (v : Fin 2 → Γ(M,Z.left)),
      dualPairing (Scheme.Modules.exteriorPower M (2:ℤ)) lam Z
        (exteriorWedgeAlternating M Z.left v) =
      dualPairing (Scheme.Modules.exteriorPower M (2:ℤ)) mu Z
        (exteriorWedgeAlternating M Z.left v)) : lam = mu := by
  apply (exteriorDualToRaw_app_bijective M U).injective
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  let F := SheafOfModules.valPresheaf (Osharp := Y.sheaf)
    (Opens.grothendieckTopology ↥Y) M
  let e := PresheafOfModules.extPowSections 2 F (op Z.unop.left)
  let a := (((exteriorDualToRaw M).val.app (op U) lam).app Z).hom
  let b := (((exteriorDualToRaw M).val.app (op U) mu).app Z).hom
  have hh : a.comp e.symm.toLinearMap = b.comp e.symm.toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hz := h Z.unop (fun j => siteSectionSemilinearEquiv M Z.unop.left (v j))
    rw [exteriorWedgeAlternating_raw] at hz
    exact hz
  apply LinearMap.ext
  intro z
  have hz := LinearMap.congr_fun hh (e z)
  exact (congrArg a (e.symm_apply_apply z)).symm.trans
    (hz.trans (congrArg b (e.symm_apply_apply z)))
lemma bivectorSectionBracket_natural {Y B : Scheme.{u}} (f : Y ⟶ B)
    {U V : Y.Opens} (h : V ≤ U) (pi : Γ(bivectorSheaf f,U)) (a b : Γ(Y,U)) :
    Y.presheaf.map (homOfLE h).op (bivectorSectionBracket f U pi a b) =
      bivectorSectionBracket f V ((bivectorSheaf f).val.map (homOfLE h).op pi)
        (Y.presheaf.map (homOfLE h).op a) (Y.presheaf.map (homOfLE h).op b) := by
  exact (contractionSectionBracket_natural f h _ a b).trans
    (congrArg (fun c => contractionSectionBracket f V c
      (Y.presheaf.map (homOfLE h).op a) (Y.presheaf.map (homOfLE h).op b))
      (PresheafOfModules.naturality_apply (bivectorContraction f).val (homOfLE h).op pi).symm)

def bivectorFunctionPairing {Y B : Scheme.{u}} (f : Y ⟶ B)
    (U : Y.Opens) (a b : Γ(Y,U)) : Γ(dualSheaf (bivectorSheaf f),U) :=
  localHomOfFamily (bivectorSheaf f) (SheafOfModules.unit Y.ringCatSheaf) U
    (fun V h pi => bivectorSectionBracket f V pi
      (Y.presheaf.map (homOfLE h).op a) (Y.presheaf.map (homOfLE h).op b))
    (fun V h pi tau => bivectorSectionBracket_add f V pi tau _ _)
    (fun V h r pi => bivectorSectionBracket_smul f V r pi _ _)
    (fun V W hVW hWU pi => by
      have hn := bivectorSectionBracket_natural f hVW pi
        (Y.presheaf.map (homOfLE hWU).op a) (Y.presheaf.map (homOfLE hWU).op b)
      have ha := congrArg (fun k => k a) (Y.presheaf.map_comp (homOfLE hWU).op (homOfLE hVW).op)
      have hb := congrArg (fun k => k b) (Y.presheaf.map_comp (homOfLE hWU).op (homOfLE hVW).op)
      change Y.presheaf.map (homOfLE (hVW.trans hWU)).op a =
        Y.presheaf.map (homOfLE hVW).op (Y.presheaf.map (homOfLE hWU).op a) at ha
      change Y.presheaf.map (homOfLE (hVW.trans hWU)).op b =
        Y.presheaf.map (homOfLE hVW).op (Y.presheaf.map (homOfLE hWU).op b) at hb
      rw [← ha,← hb] at hn
      exact hn.symm)

lemma bivectorFunctionPairing_eval_subopen {Y B : Scheme.{u}} (f : Y ⟶ B)
    (U : Y.Opens) (a b : Γ(Y,U)) (Z : Over U) (pi : Γ(bivectorSheaf f,Z.left)) :
    dualPairing (bivectorSheaf f) (bivectorFunctionPairing f U a b) Z pi =
      bivectorSectionBracket f Z.left pi (Y.presheaf.map Z.hom.op a)
        (Y.presheaf.map Z.hom.op b) := rfl

lemma bivectorFunctionPairing_eval {Y B : Scheme.{u}} (f : Y ⟶ B)
    (U : Y.Opens) (a b : Γ(Y,U)) (pi : Γ(bivectorSheaf f,U)) :
    dualPairing (bivectorSheaf f) (bivectorFunctionPairing f U a b) (Over.mk (𝟙 U)) pi =
      bivectorSectionBracket f U pi a b := by
  change bivectorSectionBracket f U pi (Y.presheaf.map (𝟙 (op U)) a)
    (Y.presheaf.map (𝟙 (op U)) b) = _
  rw [Y.presheaf.map_id]
  rfl
end NcCubic.Geometry.ImmersionBracketNaturality
