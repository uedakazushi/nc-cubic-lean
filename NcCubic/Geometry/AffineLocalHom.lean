/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local affine section comparisons; pinned upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.LocalHomFamily
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineRestrictSections
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
/-- Actual affine-open fullness and faithfulness for the over-category internal Hom. -/
theorem localHomFamily_eval_bijective [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hU : IsAffineOpen U) :
    Function.Bijective (fun t : (restrFun X.sheaf.obj U).obj M.val ⟶
      (restrFun X.sheaf.obj U).obj N.val => localHomFamily M N U t U le_rfl) := by
  constructor
  · intro t t' h
    have hf := Stacks.AlgebraicGeometry.ModuleLimits.sectionFamily_ext_of_isAffineOpen
      (M := M) (N := N) hU
      (fun V h => localHomFamily M N U t V h)
      (fun V h => localHomFamily M N U t' V h)
      (fun V h => (localHomFamily M N U t V h).map_add)
      (fun V h => (localHomFamily M N U t V h).map_smul)
      (localHomFamily_restrict M N U t)
      (fun V h => (localHomFamily M N U t' V h).map_add)
      (fun V h => (localHomFamily M N U t' V h).map_smul)
      (localHomFamily_restrict M N U t')
      (fun a => LinearMap.congr_fun h a)
    apply PresheafOfModules.hom_ext
    intro Z
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change localHomFamily M N U t Z.unop.left (leOfHom Z.unop.hom) a =
      localHomFamily M N U t' Z.unop.left (leOfHom Z.unop.hom) a
    exact hf _ _ a
  · intro f
    obtain ⟨t,hadd,hsmul,hres,htop⟩ :=
      Stacks.AlgebraicGeometry.ModuleLimits.exists_sectionFamily_of_isAffineOpen hU f
    refine ⟨localHomOfFamily M N U t hadd hsmul hres, ?_⟩
    apply LinearMap.ext
    exact htop
end NcCubic.Geometry
