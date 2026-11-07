/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
/- Adapted from pinned Stacks WeilCohomology.LambdaOperations,
5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache 2.0.
Only the local free exterior-power argument is used, without K-group imports. -/
module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
set_option maxHeartbeats 1000000
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

section Generic
universe v u₁
variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  {F : SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}
/-- The exterior power of a finite locally free sheaf is finite locally free; rank may vary. -/
theorem exterior_finiteLocallyFree_generic
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    (hF : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,v,u₁} F) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,v,u₁} (A.exteriorPower n) := by
  classical
  have _hP : ∀ (U : C) (K : Type u), HasColimitsOfShape (Discrete K)
      (PresheafOfModules.{u} ((Sheaf.toRingCat J Osharp).over U).obj) :=
    fun _ _ => PresheafOfModules.hasColimitsOfShape _ _
  obtain ⟨q,hq,hft⟩ := hF.exists_isFiniteLocallyFreeData
  let _lo : ∀ i : q.I, LinearOrder ((q.generators i).I) :=
    fun _ => IsWellOrder.linearOrder WellOrderingRel
  have E : ∀ i : q.I, SheafOfModules.free
      (R := (Sheaf.toRingCat J Osharp).over (q.X i)) ↥(Set.powersetCard ((q.generators i).I) n) ≅
      (A.exteriorPower n).over (q.X i) := fun i => by
    letI := hq.isIso i
    exact (Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree A (q.X i) n ((q.generators i).I)
      (asIso (q.generators i).π).symm).symm
  refine ⟨⟨q.I,q.X,q.coversTop,fun i =>
      ⟨↥(Set.powersetCard ((q.generators i).I) n),
        ((A.exteriorPower n).over (q.X i)).freeHomEquiv (E i).hom,
        by rw [Equiv.symm_apply_apply]; exact IsIso.epi_of_iso _⟩⟩,
    ⟨fun i => by
      dsimp only [SheafOfModules.GeneratingSections.π]
      rw [Equiv.symm_apply_apply]
      infer_instance⟩,
    ⟨fun i => ?_⟩⟩
  have : Finite ((q.generators i).I) := (hft.isFiniteType i).finite
  exact ⟨inferInstance⟩
end Generic

theorem exterior_finiteLocallyFree {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    (hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u} M) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Modules.exteriorPower M (n:ℤ)) := by
  have hM' : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u}
      (R := Sheaf.toRingCat (Opens.grothendieckTopology ↥X) X.sheaf) M := hM
  exact exterior_finiteLocallyFree_generic (Osharp := X.sheaf)
    (SheafOfModules.algebras (Opens.grothendieckTopology ↥X) M) n hM'

/-- The two standard finite-locally-free spellings agree in the direction needed here. -/
theorem stackFiniteLocallyFree_of_finiteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u} M :=
  ⟨hM.exists_isFiniteLocallyFreeData⟩
end NcCubic.Geometry
