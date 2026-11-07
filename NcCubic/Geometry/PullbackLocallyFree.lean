/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Focused adaptation of finite locally free base change and finite presentation
from pinned AxiomMath/Stacks 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
VirtualNormalBundleBaseChange.lean and FiniteLocallyFreeTFAE.lean (Apache-2.0).
No virtual-normal-bundle or conormal module is imported.
-/
module
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Rank
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace NcCubic.Geometry.PullbackDual
noncomputable section
variable {X Y : Scheme.{u}}

/-- Finite locally free data gives a presentation with finite generators
and an empty family of relations on each member of the cover. -/
theorem isFinitePresentation_of_isFiniteLocallyFree {S : Scheme.{u}} (M : S.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M) :
    M.IsFinitePresentation := by
  obtain ⟨q, hq, hfinite⟩ := h.exists_isFiniteLocallyFreeData
  let _ : q.IsLocallyFreeData := hq
  let σ := q.quasiCoherentData
  apply SheafOfModules.IsFinitePresentation.mk
  refine ⟨σ, ?_⟩
  constructor
  intro i
  constructor
  · change (q.generators i).IsFiniteType
    exact ⟨(hfinite.isFiniteType i).finite⟩
  · change (σ.presentation i).relations.IsFiniteType
    have hrel : Finite (ULift.{u,0} Empty) := by
      let _ : Finite Empty := inferInstance
      exact Finite.of_equiv Empty Equiv.ulift.symm
    exact ⟨hrel⟩

/-- The pullback of a finite locally free sheaf of modules along a morphism of sites coming
from a continuous map of spaces is finite locally free: the local free presentations transport
with the same finite index types. -/
@[ega "III 7.7.9" "partial"]
theorem isFiniteLocallyFree_pullbackData {T T' : TopCat.{u}} (f : T ⟶ T')
    {S : Sheaf (Opens.grothendieckTopology T') RingCat.{u}}
    {R : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat _ _).obj R)
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    (M : SheafOfModules.{u} S)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((SheafOfModules.pullback φ).obj M) := by
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  choose G hG eUnit eM using fun i ↦
    Stacks.AlgebraicGeometry.ComponentDegrees.exists_pullbackOver f φ M (q.X i)
  refine { exists_isFiniteLocallyFreeData := ⟨{
      I := q.I
      X := fun i ↦ (Opens.map f).obj (q.X i)
      coversTop := (Opens.coversTop_iff _ _).2
        (((Opens.coversTop_iff _ _).1 q.coversTop).comap f.hom)
      generators := fun i ↦
        ((q.generators i).map (G i) (eUnit i).some).ofEpi (eM i).some.hom }, ?_, ?_⟩ }
  · constructor
    intro i
    have h0 : IsIso (q.generators i).π := hq.isIso i
    have h2 : IsIso (((q.generators i).map (G i) (eUnit i).some).π ≫ (eM i).some.hom) :=
      inferInstance
    exact Eq.mpr (congrArg IsIso (SheafOfModules.GeneratingSections.ofEpi_π
      ((q.generators i).map (G i) (eUnit i).some) (eM i).some.hom)) h2
  · constructor
    intro i
    have : (q.generators i).IsFiniteType := hfin.isFiniteType i
    infer_instance

/-- **The pullback of a finite locally free module along a morphism of schemes is finite
locally free.** -/
theorem isFiniteLocallyFree_pullback (g : X ⟶ Y) (M : Y.Modules)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback g).obj M) :=
  by
    let _ : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
      (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
    exact isFiniteLocallyFree_pullbackData _ g.toRingCatSheafHom M h


end
end NcCubic.Geometry.PullbackDual
