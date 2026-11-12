module
public import NcCubic.Geometry.ExteriorFunctionalPairing
public import NcCubic.Geometry.ContractionEvaluation
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false
variable {X S : Scheme.{u}} (f : X ⟶ S)
theorem functional_res_comp (M : X.Modules) {U V W : X.Opens}
    (h : W≤V) (k : V≤U) (a : Γ(M,U)) :
    M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE k).op a) =
      M.presheaf.map (homOfLE (h.trans k)).op a := by
  rw [← ConcreteCategory.comp_apply,← M.presheaf.map_comp]
  rfl
variable (lam : Γ(dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)),⊤))

def functionalTangentLocal (U : X.Opens) (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    Γ(tangentSheaf f,U) :=
  localHomOfFamily (Scheme.Hom.relativeDifferentials f) (SheafOfModules.unit (structureSheaf X.sheaf)) U
    (fun V h b => exteriorFunctionalPairing f lam V
      ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op a) b)
    (fun V _h b c => (exteriorFunctionalPairing f lam V _).map_add b c)
    (fun V _h r b => (exteriorFunctionalPairing f lam V _).map_smul r b)
    (fun V _W hVW hWU b =>
      (congrArg (fun q => exteriorFunctionalPairing f lam V q
        ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE hVW).op b))
          (functional_res_comp (Scheme.Hom.relativeDifferentials f) hVW hWU a).symm).trans
        (exteriorFunctionalPairing_natural f lam hVW _ b).symm)

theorem functionalTangentLocal_add (U : X.Opens) (a b : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    functionalTangentLocal f lam U (a+b) = functionalTangentLocal f lam U a + functionalTangentLocal f lam U b := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map Z.unop.hom.op (a+b)) c =
    exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map Z.unop.hom.op a) c +
    exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map Z.unop.hom.op b) c
  simp only [map_add,LinearMap.add_apply]

theorem functionalTangentLocal_smul (U : X.Opens) (r : Γ(X,U)) (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    functionalTangentLocal f lam U (r • a) = r • functionalTangentLocal f lam U a := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map Z.unop.hom.op (r • a)) b =
    ((smulHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
      (SheafOfModules.unit (structureSheaf X.sheaf)).val U r (functionalTangentLocal f lam U a)).app Z).hom b
  simp only [smulHom]
  change exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map Z.unop.hom.op (r • a)) b =
    (X.presheaf.map Z.unop.hom.op r) * exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map Z.unop.hom.op a) b
  rw [(Scheme.Hom.relativeDifferentials f).map_smul]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]

theorem functionalTangentLocal_natural {U V : X.Opens} (h : V≤U)
    (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (tangentSheaf f).presheaf.map (homOfLE h).op (functionalTangentLocal f lam U a) =
      functionalTangentLocal f lam V ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op a) := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  change exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map (Z.unop.hom ≫ homOfLE h).op a) b =
    exteriorFunctionalPairing f lam Z.unop.left
      ((Scheme.Hom.relativeDifferentials f).presheaf.map Z.unop.hom.op
        ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op a)) b
  exact congrArg (fun q => exteriorFunctionalPairing f lam Z.unop.left q b)
    (congrArg (fun k => k a) ((Scheme.Hom.relativeDifferentials f).presheaf.map_comp (homOfLE h).op Z.unop.hom.op))

/-- Contract a genuine global exterior-cotangent functional with an actual differential. -/
def exteriorFunctionalContraction : Γ(tangentContractionSheaf f,⊤) :=
  localHomOfFamily (Scheme.Hom.relativeDifferentials f) (tangentSheaf f) ⊤
    (fun U _ => functionalTangentLocal f lam U)
    (fun U _ => functionalTangentLocal_add f lam U)
    (fun U _ => functionalTangentLocal_smul f lam U)
    (fun _ _ h _ a => (functionalTangentLocal_natural f lam h a).symm)

theorem exteriorFunctionalContraction_eval (U : X.Opens)
    (a b : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    tangentEvaluation f U
      (contractionEvaluation f U ((tangentContractionSheaf f).presheaf.map (homOfLE le_top).op
        (exteriorFunctionalContraction f lam)) a) b = exteriorFunctionalPairing f lam U a b := by
  change exteriorFunctionalPairing f lam U
    ((Scheme.Hom.relativeDifferentials f).presheaf.map (𝟙 (op U)) a) b = _
  rw [(Scheme.Hom.relativeDifferentials f).presheaf.map_id]
  rfl

end NcCubic.Geometry
