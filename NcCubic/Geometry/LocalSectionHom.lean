module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
set_option backward.isDefEq.respectTransparency false in
/-- All restrictions of an actual local module section, as a compatible family on the slice. -/
def localSectionFamily (s : Γ(M,U)) : ((restrFun X.sheaf.obj U).obj M.val).sections :=
  PresheafOfModules.sectionsMk
    (fun Z => M.val.map Z.unop.hom.op s)
    (by
      intro Z Z' k
      have e : (M.val.map (Z.unop.hom.op ≫ ((Over.forget U).map k.unop).op)).hom s =
          (M.val.map ((Over.forget U).map k.unop).op).hom
            ((M.val.map Z.unop.hom.op).hom s) := by
        rw [M.val.map_comp]
        rfl
      have hw : Z.unop.hom.op ≫ ((Over.forget U).map k.unop).op = Z'.unop.hom.op := by
        rw [← op_comp]
        exact congrArg Quiver.Hom.op (Over.w k.unop)
      exact e.symm.trans (PresheafOfModules.congr_map_apply M.val hw s))
/-- Multiplication by a local section is an actual morphism of restricted module presheaves. -/
def localSectionHom (s : Γ(M,U)) :
    (restrFun X.sheaf.obj U).obj (SheafOfModules.unit (structureSheaf X.sheaf)).val ⟶
      (restrFun X.sheaf.obj U).obj M.val :=
  ((restrFun X.sheaf.obj U).obj M.val).unitHomEquiv.symm (localSectionFamily M U s)
@[simp] theorem localSectionHom_app (s : Γ(M,U)) (Z : (Over U)ᵒᵖ)
    (r : Γ(X,Z.unop.left)) :
    (localSectionHom M U s).app Z r = r • (show Γ(M,Z.unop.left) from (M.val.map Z.unop.hom.op).hom s) := by
  rfl

/-- The local multiplication maps commute with all restriction maps. -/
theorem localSectionHom_restrict_apply (s : Γ(M,U))
    {Z Z' : (Over U)ᵒᵖ} (k : Z ⟶ Z')
    (r : ((restrFun X.sheaf.obj U).obj
      (SheafOfModules.unit (structureSheaf X.sheaf)).val).obj Z) :
    (((restrFun X.sheaf.obj U).obj M.val).map k)
      ((localSectionHom M U s).app Z r) =
    (localSectionHom M U s).app Z'
      ((((restrFun X.sheaf.obj U).obj
        (SheafOfModules.unit (structureSheaf X.sheaf)).val).map k) r) := by
  exact (PresheafOfModules.naturality_apply (localSectionHom M U s) k r).symm

@[simp] theorem localSectionHom_zero : localSectionHom M U 0 = 0 := by
  ext Z
  change (localSectionHom M U 0).app Z (1 : Γ(X,Z.unop.left)) = 0
  rw [localSectionHom_app]
  have hh : (show Γ(M,Z.unop.left) from (M.val.map Z.unop.hom.op).hom (0 : Γ(M,U))) = 0 :=
    (M.val.map Z.unop.hom.op).hom.map_zero
  rw [hh, smul_zero]
  rfl
@[simp] theorem localSectionHom_add (s t : Γ(M,U)) :
    localSectionHom M U (s+t) = localSectionHom M U s + localSectionHom M U t := by
  ext Z
  change (localSectionHom M U (s+t)).app Z (1 : Γ(X,Z.unop.left)) =
    (localSectionHom M U s).app Z (1 : Γ(X,Z.unop.left)) +
      (localSectionHom M U t).app Z (1 : Γ(X,Z.unop.left))
  rw [localSectionHom_app,localSectionHom_app,localSectionHom_app]
  have hh : (show Γ(M,Z.unop.left) from (M.val.map Z.unop.hom.op).hom (s+t)) =
      (show Γ(M,Z.unop.left) from (M.val.map Z.unop.hom.op).hom s) +
        (show Γ(M,Z.unop.left) from (M.val.map Z.unop.hom.op).hom t) :=
    (M.val.map Z.unop.hom.op).hom.map_add s t
  rw [hh,smul_add]
  rfl

end NcCubic.Geometry
