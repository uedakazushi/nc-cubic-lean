module
public import NcCubic.Geometry.ProjectiveExteriorFrame
public import NcCubic.Geometry.TwistSumSections
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace NcCubic.Geometry.FiniteSections
universe u
variable {R : Type u} [CommRing R] {C : Type*} [Category C] [Preadditive C]

/-- Canonical section coordinates for an arbitrarily indexed finite biproduct. -/
def biproductEquiv {I : Type} [Fintype I] (F : C ⥤ ModuleCat.{u} R) [F.Additive]
    (L : I → C) [HasBiproduct L] :
    F.obj (⨁ L) ≃ₗ[R] (∀ i, F.obj (L i)) :=
  ((F.mapBiproduct L) ≪≫ ModuleCat.biproductIsoPi (fun i => F.obj (L i))).toLinearEquiv

@[simp] theorem biproductEquiv_component {I : Type} [Fintype I]
    (F : C ⥤ ModuleCat.{u} R) [F.Additive] (L : I → C) [HasBiproduct L]
    (s : F.obj (⨁ L)) (i : I) :
    biproductEquiv F L s i = (F.map (biproduct.π L i)).hom s := by
  have hh : ((F.mapBiproduct L) ≪≫ ModuleCat.biproductIsoPi (fun i => F.obj (L i))).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = F.map (biproduct.π L i) := by
    have hp : (ModuleCat.biproductIsoPi (fun i => F.obj (L i))).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) = biproduct.π (fun i => F.obj (L i)) i := by
      apply (cancel_epi (ModuleCat.biproductIsoPi (fun i => F.obj (L i))).inv).1
      simp
    simp only [Iso.trans_hom, Category.assoc, hp, Functor.mapBiproduct_hom, biproduct.lift_π]
  exact congrArg (fun f => f.hom s) hh

/-- The inverse uses the original inclusions, without a reindexing choice. -/
theorem biproductEquiv_symm {I : Type} [Fintype I]
    (F : C ⥤ ModuleCat.{u} R) [F.Additive] (L : I → C) [HasBiproduct L]
    (s : ∀ i, F.obj (L i)) :
    (biproductEquiv F L).symm s = ∑ i, (F.map (biproduct.ι L i)).hom (s i) := by
  classical
  apply (biproductEquiv F L).injective
  ext j
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_sum, biproductEquiv_component]
  simp only [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← F.map_comp, biproduct.ι_π]
  symm
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

end NcCubic.Geometry.FiniteSections

namespace NcCubic.Geometry.ProjectiveQuadraticSections
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.ProjectiveSpace.Cohomology
open ProjectiveExteriorFrame
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
universe u
variable (R : Type u) [CommRing R] (n N : ℕ)

/-- Canonical quadratic polynomial coefficients of an actual global section
of the exterior square of the positive twist sum. -/
def quadraticSectionsEquiv :
    (twistCoefficientSections R n).obj (wedge R n (twistSum R n 1 N) 2) ≃ₗ[R]
      (Set.powersetCard (Fin N) 2 →
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 2) :=
  (((twistCoefficientSections R n).mapIso (quadraticCoordinateIso R n N)).toLinearEquiv).trans
    ((FiniteSections.biproductEquiv (twistCoefficientSections R n)
      (fun _ : Set.powersetCard (Fin N) 2 => twistObj R n 2)).trans
        (LinearEquiv.piCongrRight fun _ => (degreeSectionEquiv R n 2).symm))

/-- Each extracted polynomial is carried by the original canonical degree-section
map to the actual corresponding quadratic projection section. -/
theorem quadraticSectionsEquiv_component
    (σ : (twistCoefficientSections R n).obj (wedge R n (twistSum R n 1 N) 2))
    (s : Set.powersetCard (Fin N) 2) :
    degreeSectionLinear R n 2 (quadraticSectionsEquiv R n N σ s) =
      ((twistCoefficientSections R n).map (quadraticProjection R n N s)).hom σ := by
  change degreeSectionEquiv R n 2 ((degreeSectionEquiv R n 2).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  refine (FiniteSections.biproductEquiv_component (twistCoefficientSections R n)
    (fun _ : Set.powersetCard (Fin N) 2 => twistObj R n 2) _ s).trans ?_
  change ((twistCoefficientSections R n).map (biproduct.π _ s)).hom
    (((twistCoefficientSections R n).map (quadraticCoordinateIso R n N).hom).hom σ) = _
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp,
    quadraticCoordinateIso_projection]

/-- The inverse is the explicit sum of the actual ordered coordinate components
applied to the original degree-section map of each polynomial coefficient. -/
theorem quadraticSectionsEquiv_symm
    (a : Set.powersetCard (Fin N) 2 →
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 2) :
    (quadraticSectionsEquiv R n N).symm a =
      ∑ s, ((twistCoefficientSections R n).map (quadraticComponent R n N s)).hom
        (degreeSectionLinear R n 2 (a s)) := by
  change ((twistCoefficientSections R n).map (quadraticCoordinateIso R n N).inv).hom
    ((FiniteSections.biproductEquiv (twistCoefficientSections R n)
      (fun _ : Set.powersetCard (Fin N) 2 => twistObj R n 2)).symm
        (fun s => degreeSectionLinear R n 2 (a s))) = _
  rw [FiniteSections.biproductEquiv_symm, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← Functor.map_comp,
    inclusion_quadraticCoordinateIso_inv]

/-- Every actual global exterior section is reconstructed from its canonical
homogeneous quadratic coefficients. -/
theorem quadraticSections_reconstruct
    (σ : (twistCoefficientSections R n).obj (wedge R n (twistSum R n 1 N) 2)) :
    ∑ s, ((twistCoefficientSections R n).map (quadraticComponent R n N s)).hom
      (degreeSectionLinear R n 2 (quadraticSectionsEquiv R n N σ s)) = σ := by
  rw [← quadraticSectionsEquiv_symm, LinearEquiv.symm_apply_apply]

/-- A nonzero actual exterior section has a nonzero canonical polynomial coefficient. -/
theorem exists_nonzero_quadraticCoefficient
    (σ : (twistCoefficientSections R n).obj (wedge R n (twistSum R n 1 N) 2))
    (hσ : σ ≠ 0) :
    ∃ s, quadraticSectionsEquiv R n N σ s ≠ 0 := by
  classical
  by_contra h
  have hz : quadraticSectionsEquiv R n N σ = 0 := by
    funext s
    change quadraticSectionsEquiv R n N σ s = 0
    exact not_not.mp (fun hs => h ⟨s, hs⟩)
  apply hσ
  apply (quadraticSectionsEquiv R n N).injective
  simpa only [map_zero] using hz

end NcCubic.Geometry.ProjectiveQuadraticSections
