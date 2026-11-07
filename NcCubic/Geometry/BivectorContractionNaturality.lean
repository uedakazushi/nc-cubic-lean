module
public import NcCubic.Geometry.BivectorContraction
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
private theorem localHom_restrict_comp {C : Type u} [Category C]
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) (F G H : PresheafOfModules (Oforget O))
    {U V : C} (h : V ⟶ U)
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G)
    (β : (restrFun O U).obj G ⟶ (restrFun O U).obj H) :
    homRestr O F H h (α ≫ β) = homRestr O F G h α ≫ homRestr O G H h β := by
  rw [homRestr, homRestr, homRestr, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
private theorem localHom_restrict_sub {C : Type u} [Category C]
    (O : Cᵒᵖ ⥤ CommRingCat.{u}) (F G : PresheafOfModules (Oforget O))
    {U V : C} (h : V ⟶ U)
    (α β : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    homRestr O F G h (α-β) = homRestr O F G h α - homRestr O F G h β := by
  have : (relocRestr O h).Additive := by
    constructor
    intro M N a b
    apply PresheafOfModules.hom_ext
    intro W
    rfl
  unfold homRestr
  rw [(relocRestr O h).map_sub (f := α) (g := β), Preadditive.sub_comp, Preadditive.comp_sub]

set_option backward.isDefEq.respectTransparency false in
theorem wedgeContractionLocal_restrict {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : X.Opens} (h : V ⟶ U) (v : Fin 2 → Γ(tangentSheaf f,U)) :
    homRestr X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val (tangentSheaf f).val h
      (wedgeContractionLocal f U v) =
    wedgeContractionLocal f V (fun i => (tangentSheaf f).presheaf.map h.op (v i)) := by
  unfold wedgeContractionLocal
  rw [localHom_restrict_sub, localHom_restrict_comp, localHom_restrict_comp,
    localSectionHom_restrict, localSectionHom_restrict]
  rfl
end NcCubic.Geometry
