/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local canonical direct-sum section comparison; upstream dependencies retain their licenses. -/
module
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSectionsAreForms
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {R : Type u} [CommRing R] {C : Type*} [Category C] [Preadditive C]
/-- Canonical sections-to-components comparison for any finite biproduct and additive module functor. -/
def finiteBiproductSectionsEquiv {r : ℕ} (F : C ⥤ ModuleCat.{u} R) [F.Additive]
    (L : Fin r → C) [HasBiproduct L] :
    F.obj (⨁ L) ≃ₗ[R] (∀ i, F.obj (L i)) :=
  ((F.mapBiproduct L) ≪≫ ModuleCat.biproductIsoPi (fun i => F.obj (L i))).toLinearEquiv
@[simp] theorem finiteBiproductSectionsEquiv_component {r : ℕ}
    (F : C ⥤ ModuleCat.{u} R) [F.Additive] (L : Fin r → C) [HasBiproduct L]
    (s : F.obj (⨁ L)) (i : Fin r) :
    finiteBiproductSectionsEquiv F L s i = (F.map (biproduct.π L i)).hom s := by
  have hh : ((F.mapBiproduct L) ≪≫ ModuleCat.biproductIsoPi (fun i => F.obj (L i))).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) = F.map (biproduct.π L i) := by
    have hp : (ModuleCat.biproductIsoPi (fun i => F.obj (L i))).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) = biproduct.π (fun i => F.obj (L i)) i := by
      apply (cancel_epi (ModuleCat.biproductIsoPi (fun i => F.obj (L i))).inv).1
      simp
    simp only [Iso.trans_hom,Category.assoc,hp,Functor.mapBiproduct_hom,biproduct.lift_π]
  exact congrArg (fun f => f.hom s) hh

theorem finiteBiproductSectionsEquiv_symm {r : ℕ}
    (F : C ⥤ ModuleCat.{u} R) [F.Additive] (L : Fin r → C) [HasBiproduct L]
    (s : ∀ i, F.obj (L i)) :
    (finiteBiproductSectionsEquiv F L).symm s =
      ∑ i, (F.map (biproduct.ι L i)).hom (s i) := by
  apply (finiteBiproductSectionsEquiv F L).injective
  ext j
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_sum,finiteBiproductSectionsEquiv_component]
  simp only [←LinearMap.comp_apply,←ModuleCat.hom_comp,←F.map_comp,biproduct.ι_π]
  symm
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim


end NcCubic.Geometry

namespace NcCubic.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.ProjectiveSpace.Cohomology
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
/-- Global sections with the actual coefficient action through projective space's structure morphism. -/
def twistCoefficientSections : ProjModules R n ⥤ ModuleCat.{u} R :=
  Stacks.Cohomology.sectionsFunctor (Proj (polyGrading R n)) ⊤ ⋙
    ModuleCat.restrictScalars (coeffScalar R n)

instance : (twistCoefficientSections R n).Additive := by
  exact ⟨by intros; rfl⟩

/-- The canonical degree-section map, upgraded using its proved bijectivity. -/
def degreeSectionEquiv (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n+1)) R d ≃ₗ[R]
      twistSectionsModule R n (d:ℤ) :=
  LinearEquiv.ofBijective (degreeSectionLinear R n d) (bijective_degreeSectionLinear n d)

@[simp] theorem degreeSectionEquiv_apply (d : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n+1)) R d) :
    degreeSectionEquiv R n d a = degreeSectionLinear R n d a := rfl

/-- Actual global sections of a finite twist sum are canonically homogeneous polynomial families. -/
def twistSumSectionsEquiv (d r : ℕ) :
    (twistCoefficientSections R n).obj (twistSum R n (d:ℤ) r) ≃ₗ[R]
      (Fin r → MvPolynomial.homogeneousSubmodule (Fin (n+1)) R d) :=
  (finiteBiproductSectionsEquiv (twistCoefficientSections R n) (twistFamily R n (d:ℤ) r)).trans
    (LinearEquiv.piCongrRight (fun _ => (degreeSectionEquiv R n d).symm))

/-- Each polynomial coefficient gives exactly the corresponding original biproduct projection. -/
theorem twistSumSectionsEquiv_component (d r : ℕ)
    (s : (twistCoefficientSections R n).obj (twistSum R n (d:ℤ) r)) (i : Fin r) :
    degreeSectionLinear R n d (twistSumSectionsEquiv R n d r s i) =
      ((twistCoefficientSections R n).map (biproduct.π (twistFamily R n (d:ℤ) r) i)).hom s := by
  change degreeSectionEquiv R n d ((degreeSectionEquiv R n d).symm _) = _
  exact ((degreeSectionEquiv R n d).apply_symm_apply _).trans
    (finiteBiproductSectionsEquiv_component _ _ s i)

/-- The inverse is the sum of the original biproduct inclusions of the canonical degree sections. -/
theorem twistSumSectionsEquiv_symm (d r : ℕ)
    (a : Fin r → MvPolynomial.homogeneousSubmodule (Fin (n+1)) R d) :
    (twistSumSectionsEquiv R n d r).symm a =
      ∑ i, ((twistCoefficientSections R n).map
        (biproduct.ι (twistFamily R n (d:ℤ) r) i)).hom (degreeSectionLinear R n d (a i)) :=
  finiteBiproductSectionsEquiv_symm (twistCoefficientSections R n)
    (twistFamily R n (d:ℤ) r) (fun i => degreeSectionLinear R n d (a i))

/-- The same canonical equivalence for any nonnegative integer twist. -/
def twistSumSectionsEquivOfNonneg (d : ℤ) (hd : 0 ≤ d) (r : ℕ) :
    (twistCoefficientSections R n).obj (twistSum R n d r) ≃ₗ[R]
      (Fin r → MvPolynomial.homogeneousSubmodule (Fin (n+1)) R d.toNat) := by
  have he : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd
  exact (((twistCoefficientSections R n).mapIso
    (eqToIso (congrArg (fun z => twistSum R n z r) he))).symm.toLinearEquiv).trans
      (twistSumSectionsEquiv R n d.toNat r)
end NcCubic.Geometry
