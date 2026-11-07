module
public import NcCubic.Geometry.ProjectiveBivector
public import NcCubic.Geometry.LocalSectionHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import Mathlib.Tactic.FinCases
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
private theorem multEndoHom_comm {C : Type u} [Category C]
    (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (F G : PresheafOfModules (Oforget O)) (U : C) (c : (Oforget O).obj (op U))
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G) :
    multEndoHom O F U c ≫ α = α ≫ multEndoHom O G U c := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change α.app W (fRestr O U c W • x) = fRestr O U c W • α.app W x
  exact (α.app W).hom.map_smul _ _

private theorem smulHom_comp {C : Type u} [Category C]
    (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (F G H : PresheafOfModules (Oforget O)) (U : C) (c : (Oforget O).obj (op U))
    (α : (restrFun O U).obj F ⟶ (restrFun O U).obj G)
    (β : (restrFun O U).obj G ⟶ (restrFun O U).obj H) :
    smulHom O F G U c α ≫ β = smulHom O F H U c (α ≫ β) := by
  rw [smulHom, smulHom, Category.assoc, multEndoHom_comm, Category.assoc]

/-- The actual sheaf of linear maps from relative differentials to tangent fields. -/
def tangentContractionSheaf {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules where
  val := internalHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val (tangentSheaf f).val
  isSheaf := internalHom_isSheaf X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
    (tangentSheaf f).val (tangentSheaf f).isSheaf
/-- Contract a wedge of two actual local tangent fields with a differential. -/
def wedgeContractionLocal {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (v : Fin 2 → Γ(tangentSheaf f,U)) : Γ(tangentContractionSheaf f,U) :=
  v 0 ≫ localSectionHom (tangentSheaf f) U (v 1) -
    v 1 ≫ localSectionHom (tangentSheaf f) U (v 0)

theorem wedgeContractionLocal_app {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (v : Fin 2 → Γ(tangentSheaf f,U)) (Z : (Over U)ᵒᵖ)
    (a : Γ(Scheme.Hom.relativeDifferentials f,Z.unop.left)) :
    (wedgeContractionLocal f U v).app Z a =
      (show Γ(X,Z.unop.left) from (v 0).app Z a) • (tangentSheaf f).presheaf.map Z.unop.hom.op (v 1) -
      (show Γ(X,Z.unop.left) from (v 1).app Z a) • (tangentSheaf f).presheaf.map Z.unop.hom.op (v 0) := by
  change (localSectionHom (tangentSheaf f) U (v 1)).app Z ((v 0).app Z a) -
    (localSectionHom (tangentSheaf f) U (v 0)).app Z ((v 1).app Z a) = _
  rw [localSectionHom_app, localSectionHom_app]
  rfl
set_option maxHeartbeats 1200000 in
/-- The sheaf contraction is alternating and linear in both local tangent fields. -/
def wedgeContractionAlternating {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) :
    AlternatingMap Γ(X,U) Γ(tangentSheaf f,U) Γ(tangentContractionSheaf f,U) (Fin 2) where
  toFun := wedgeContractionLocal f U
  map_update_add' v i x y := by
    fin_cases i <;> norm_num only [wedgeContractionLocal, Function.update_apply, Fin.ext_iff]
    · change (x+y) ≫ localSectionHom (tangentSheaf f) U (v 1) -
        v 1 ≫ localSectionHom (tangentSheaf f) U (x+y) =
        (x ≫ localSectionHom (tangentSheaf f) U (v 1) - v 1 ≫ localSectionHom (tangentSheaf f) U x) +
        (y ≫ localSectionHom (tangentSheaf f) U (v 1) - v 1 ≫ localSectionHom (tangentSheaf f) U y)
      rw [localSectionHom_add, Preadditive.add_comp, Preadditive.comp_add]
      abel
    · change v 0 ≫ localSectionHom (tangentSheaf f) U (x+y) -
        (x+y) ≫ localSectionHom (tangentSheaf f) U (v 0) =
        (v 0 ≫ localSectionHom (tangentSheaf f) U x - x ≫ localSectionHom (tangentSheaf f) U (v 0)) +
        (v 0 ≫ localSectionHom (tangentSheaf f) U y - y ≫ localSectionHom (tangentSheaf f) U (v 0))
      rw [localSectionHom_add, Preadditive.add_comp, Preadditive.comp_add]
      abel
  map_update_smul' v i c x := by
    fin_cases i <;> norm_num only [wedgeContractionLocal, Function.update_apply, Fin.ext_iff]
    · change smulHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
        (SheafOfModules.unit (structureSheaf X.sheaf)).val U c x ≫
          localSectionHom (tangentSheaf f) U (v 1) -
        v 1 ≫ localSectionHom (tangentSheaf f) U (c • x) =
        smulHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val (tangentSheaf f).val U c
          (x ≫ localSectionHom (tangentSheaf f) U (v 1) -
            v 1 ≫ localSectionHom (tangentSheaf f) U x)
      rw [localSectionHom_smul, smulHom_comp]
      simp only [smulHom, Category.assoc, Preadditive.sub_comp]
    · change v 0 ≫ localSectionHom (tangentSheaf f) U (c • x) -
        smulHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
          (SheafOfModules.unit (structureSheaf X.sheaf)).val U c x ≫
            localSectionHom (tangentSheaf f) U (v 0) =
        smulHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val (tangentSheaf f).val U c
          (v 0 ≫ localSectionHom (tangentSheaf f) U x -
            x ≫ localSectionHom (tangentSheaf f) U (v 0))
      rw [localSectionHom_smul, smulHom_comp]
      simp only [smulHom, Category.assoc, Preadditive.sub_comp]
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij
      simp [wedgeContractionLocal, hij]
    · change v 1 = v 0 at hij
      simp [wedgeContractionLocal, hij]
    · exact (hne rfl).elim

end NcCubic.Geometry
