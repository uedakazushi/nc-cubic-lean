/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
The section-iso adapter is adapted from StacksFrontier.AlgebraicGeometry.QuasicoherentBasicOpen.Basic
at pinned Stacks revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache 2.0). -/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.Basis.Defs
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace NcCubic.Geometry.CotangentCoordinates
universe u
variable {X : Scheme.{u}}
noncomputable def moduleSectionsLinearEquiv {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) where
  toFun a := Scheme.Modules.Hom.app e.hom V a
  map_add' a b := by exact map_add _ a b
  map_smul' r a := Scheme.Modules.Hom.app_smul e.hom r a
  invFun a := Scheme.Modules.Hom.app e.inv V a
  left_inv a := by
    have h : Scheme.Modules.Hom.app e.hom V ≫ Scheme.Modules.Hom.app e.inv V = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
    calc Scheme.Modules.Hom.app e.inv V (Scheme.Modules.Hom.app e.hom V a)
        = (Scheme.Modules.Hom.app e.hom V ≫ Scheme.Modules.Hom.app e.inv V) a :=
          (ConcreteCategory.comp_apply _ _ a).symm
      _ = a := by rw [h]; rfl
  right_inv a := by
    have h : Scheme.Modules.Hom.app e.inv V ≫ Scheme.Modules.Hom.app e.hom V = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
    calc Scheme.Modules.Hom.app e.hom V (Scheme.Modules.Hom.app e.inv V a)
        = (Scheme.Modules.Hom.app e.inv V ≫ Scheme.Modules.Hom.app e.hom V) a :=
          (ConcreteCategory.comp_apply _ _ a).symm
      _ = a := by rw [h]; rfl

/-- Pullback sections along an open immersion are actual sections on its image,
linearly over the image's section ring via the canonical open-immersion ring isomorphism. -/
def openPullbackSectionLinearEquiv {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) :
    letI : Module Γ(X, j ''ᵁ (⊤ : Y.Opens))
        Γ((Scheme.Modules.pullback j).obj M, (⊤ : Y.Opens)) :=
      Module.compHom _ (j.appIso (⊤ : Y.Opens)).hom.hom
    Γ((Scheme.Modules.pullback j).obj M, (⊤ : Y.Opens)) ≃ₗ[Γ(X, j ''ᵁ (⊤ : Y.Opens))]
      Γ(M, j ''ᵁ (⊤ : Y.Opens)) := by
  letI : Module Γ(X, j ''ᵁ (⊤ : Y.Opens))
      Γ((Scheme.Modules.pullback j).obj M, (⊤ : Y.Opens)) :=
    Module.compHom _ (j.appIso (⊤ : Y.Opens)).hom.hom
  let e := (Scheme.Modules.restrictFunctorIsoPullback j).app M
  let eA := (moduleSectionsLinearEquiv e.symm ⊤).toAddEquiv.trans
    (M.restrictAppIso j ⊤).addCommGroupIsoToAddEquiv
  refine { eA with map_smul' := ?_ }
  intro c x
  change (M.restrictAppIso j ⊤).hom
      (Scheme.Modules.Hom.app e.inv ⊤ ((j.appIso ⊤).hom.hom c • x)) = c • _
  rw [Scheme.Modules.Hom.app_smul]
  let y : Γ(M, j ''ᵁ (⊤ : Y.Opens)) := Scheme.Modules.Hom.app e.inv ⊤ x
  change ((j.appIso ⊤).inv.hom ((j.appIso ⊤).hom.hom c)) • y = c • y
  let eR := (j.appIso ⊤).commRingCatIsoToRingEquiv
  change eR.symm (eR c) • y = c • y
  rw [eR.symm_apply_apply]

/-- An actual affine pullback-section basis transports to the original open,
without assuming any local freeness of the original sheaf. -/
def openPullbackSectionsBasis {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) {ι : Type u}
    (b : Module.Basis ι Γ(Y, ⊤) Γ((Scheme.Modules.pullback j).obj M, (⊤ : Y.Opens))) :
    Module.Basis ι Γ(X, j ''ᵁ (⊤ : Y.Opens)) Γ(M, j ''ᵁ (⊤ : Y.Opens)) := by
  letI : Module Γ(X, j ''ᵁ (⊤ : Y.Opens))
      Γ((Scheme.Modules.pullback j).obj M, (⊤ : Y.Opens)) :=
    Module.compHom _ (j.appIso (⊤ : Y.Opens)).hom.hom
  let eR := (j.appIso ⊤).commRingCatIsoToRingEquiv
  have h : ∀ (c : Γ(Y, ⊤))
      (x : Γ((Scheme.Modules.pullback j).obj M, (⊤ : Y.Opens))),
      eR.symm c • x = c • x := by
    intro c x
    change eR (eR.symm c) • x = c • x
    rw [eR.apply_symm_apply]
  exact (b.mapCoeffs eR.symm h).map (openPullbackSectionLinearEquiv j M)

end NcCubic.Geometry.CotangentCoordinates
