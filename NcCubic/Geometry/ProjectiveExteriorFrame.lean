module
public import NcCubic.Geometry.SheafExteriorFrame
public import NcCubic.Geometry.PositiveTwistExterior
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] hasFiniteBiproducts_toRingCat
set_option backward.isDefEq.respectTransparency false
namespace NcCubic.Geometry.ProjectiveExteriorFrame
universe u
variable (R : Type u) [CommRing R] (n N : ℕ)

/-- The actual exterior coordinate decomposition with the standard ordered
pairs. Each coordinate uses the canonical multiplication O(1)⊗O(1)→O(2). -/
def quadraticCoordinateIso :
    wedge R n (twistSum R n 1 N) 2 ≅
      ⨁ (fun _ : Set.powersetCard (Fin N) 2 => twistObj R n 2) :=
  (SheafExteriorFrame.coordinateIso (twistObj R n 1) N
    (isFiniteLocallyFreeOfRank_twistingSheaf R n 1)).symm ≪≫
      biproduct.mapIso (fun _ : Set.powersetCard (Fin N) 2 =>
        tensorTwistingSheafIso R n 1 1)

/-- The canonical O(2)-valued coefficient of one ordered coordinate pair. -/
def quadraticProjection (s : Set.powersetCard (Fin N) 2) :
    wedge R n (twistSum R n 1 N) 2 ⟶ twistObj R n 2 :=
  SheafExteriorFrame.projection (twistObj R n 1) N
    (isFiniteLocallyFreeOfRank_twistingSheaf R n 1) s ≫
      (tensorTwistingSheafIso R n 1 1).hom

/-- Reconstruct a coordinate bivector from an actual quadratic-twist section. -/
def quadraticComponent (s : Set.powersetCard (Fin N) 2) :
    twistObj R n 2 ⟶ wedge R n (twistSum R n 1 N) 2 :=
  (tensorTwistingSheafIso R n 1 1).inv ≫
    SheafExteriorFrame.component (twistObj R n 1) N
      (Set.powersetCard.ofFinEmbEquiv.symm s 0)
      (Set.powersetCard.ofFinEmbEquiv.symm s 1)

@[simp] theorem quadraticCoordinateIso_projection (s : Set.powersetCard (Fin N) 2) :
    (quadraticCoordinateIso R n N).hom ≫
      biproduct.π (fun _ : Set.powersetCard (Fin N) 2 => twistObj R n 2) s =
      quadraticProjection R n N s := by
  simp [quadraticCoordinateIso, quadraticProjection, SheafExteriorFrame.projection,
    Category.assoc]

@[simp] theorem inclusion_quadraticCoordinateIso_inv (s : Set.powersetCard (Fin N) 2) :
    biproduct.ι (fun _ : Set.powersetCard (Fin N) 2 => twistObj R n 2) s ≫
      (quadraticCoordinateIso R n N).inv = quadraticComponent R n N s := by
  simp [quadraticCoordinateIso, quadraticComponent,
    SheafExteriorFrame.coordinateIso_hom]
  exact SheafExteriorFrame.inclusion_reconstruction (twistObj R n 1) N s

@[simp] theorem quadraticComponent_projection (s t : Set.powersetCard (Fin N) 2) :
    quadraticComponent R n N s ≫ quadraticProjection R n N t =
      if s = t then 𝟙 (twistObj R n 2) else 0 := by
  unfold quadraticComponent quadraticProjection
  rw [Category.assoc, ← Category.assoc _ _ (tensorTwistingSheafIso R n 1 1).hom,
    SheafExteriorFrame.component_projection]
  by_cases h : s = t <;> simp [h]

/-- The actual ordered quadratic coefficients reconstruct every exterior section. -/
theorem quadraticProjections_reconstruct :
    ∑ s : Set.powersetCard (Fin N) 2,
      quadraticProjection R n N s ≫ quadraticComponent R n N s = 𝟙 _ := by
  simp only [quadraticProjection, quadraticComponent, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact SheafExteriorFrame.projections_reconstruct (twistObj R n 1) N
      (isFiniteLocallyFreeOfRank_twistingSheaf R n 1)

end NcCubic.Geometry.ProjectiveExteriorFrame
