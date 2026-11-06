/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.TangentSheaf
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem tangentEvaluation_add (U : X.Opens) (t s : Γ(tangentSheaf f,U))
    (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    tangentEvaluation f U (t+s) a = tangentEvaluation f U t a + tangentEvaluation f U s a := rfl

theorem tangentEvaluation_smul (U : X.Opens) (r : Γ(X,U)) (t : Γ(tangentSheaf f,U))
    (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    tangentEvaluation f U (r • t) a = r * tangentEvaluation f U t a := by
  change ((smulHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
    (SheafOfModules.unit (structureSheaf X.sheaf)).val U r t).app
    (op (Over.mk (𝟙 U)))).hom a = _
  simp only [smulHom]
  change (X.presheaf.map (𝟙 (op U))) r * tangentEvaluation f U t a = _
  rw [X.presheaf.map_id]
  rfl

/-- Evaluation is linear in the genuine tangent-sheaf section. -/
def tangentEvaluationLinear (U : X.Opens) :
    Γ(tangentSheaf f,U) →ₗ[Γ(X,U)]
      Γ(Scheme.Hom.relativeDifferentials f,U) →ₗ[Γ(X,U)] Γ(X,U) where
  toFun := tangentEvaluation f U
  map_add' t s := by ext a; exact tangentEvaluation_add f U t s a
  map_smul' r t := by ext a; exact tangentEvaluation_smul f U r t a

theorem tangentEvaluation_restricted {U V : X.Opens} (h : V ≤ U)
    (t : Γ(tangentSheaf f,U)) (a : Γ(Scheme.Hom.relativeDifferentials f,V)) :
    tangentEvaluation f V ((tangentSheaf f).val.map (homOfLE h).op t) a =
      (t.app (op (Over.mk (homOfLE h)))).hom a := by
  rfl

/-- Actual tangent evaluation is compatible with restriction of both sections. -/
theorem tangentEvaluation_natural {U V : X.Opens} (h : V ≤ U)
    (t : Γ(tangentSheaf f,U)) (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (X.presheaf.map (homOfLE h).op) (tangentEvaluation f U t a) =
      tangentEvaluation f V ((tangentSheaf f).val.map (homOfLE h).op t)
        ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE h).op a) := by
  change (X.presheaf.map (homOfLE h).op) ((t.app (op (Over.mk (𝟙 U)))).hom a) =
    (t.app (op (Over.mk (homOfLE h)))).hom
      ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE h).op a)
  let g : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) := Over.homMk (homOfLE h)
  have hn := t.naturality g.op
  exact congrArg (fun k => k.hom a) hn.symm

/-- Hamiltonian action of actual tangent sections restricts on every open. -/
theorem tangentSectionDerivation_natural {U V : X.Opens} (h : V ≤ U)
    (t : Γ(tangentSheaf f,U)) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) (tangentSectionDerivation f U t a) =
      tangentSectionDerivation f V ((tangentSheaf f).val.map (homOfLE h).op t)
        ((X.presheaf.map (homOfLE h).op) a) := by
  exact (tangentEvaluation_natural f h t _).trans
    (congrArg (tangentEvaluation f V ((tangentSheaf f).val.map (homOfLE h).op t))
      ((Scheme.Hom.universalRelativeDerivation f).d_map (homOfLE h).op a).symm)

/-- Relative tangent sections annihilate base functions on arbitrary subopens,
using the actual appLE pullback rather than a chosen coefficient presentation. -/
@[simp] theorem tangentSectionDerivation_base_appLE (W : S.Opens) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ W) (t : Γ(tangentSheaf f,U)) (a : Γ(S,W)) :
    tangentSectionDerivation f U t ((f.appLE W U h).hom a) = 0 := by
  have hd := (Scheme.Hom.universalRelativeDerivation f).d_map
    (homOfLE h).op ((f.app W).hom a)
  have hz := Scheme.Hom.universalRelativeDerivation_d_app_eq_zero f W a
  rw [hz, map_zero] at hd
  exact (congrArg (tangentEvaluation f U t) hd).trans (map_zero _)
end NcCubic.Geometry
