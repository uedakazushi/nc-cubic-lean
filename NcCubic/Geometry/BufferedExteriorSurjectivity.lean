/- Surjectivity of the genuine site-buffered exterior map from the fixed
native quotient, with every factor proved for an abstract scheme. -/
module
public import NcCubic.Geometry.ExteriorSiteNativeBridge
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
namespace NcCubic.Geometry.BufferedExteriorSurjectivity
open ExteriorSiteNativeBridge
universe u v w
variable (X : Scheme.{u})
local instance : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (_root_.SheafOfModules.{u} X.ringCatSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def bufferedMap (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {Q T : X.Modules}
    (e : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ≅ Q)
    (h : Q ⟶ T) :
    (schemeModulesOfSite X).obj
      ((_root_.SheafOfModules.algebras _
        ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf)).exteriorPower q) ⟶
      Scheme.Modules.exteriorPower (X := X) T (q : ℤ) :=
  (exteriorSumIso X M N q).hom ≫
    Scheme.Modules.exteriorPowerMap (X := X) (e.hom ≫ h) (q : ℤ)

/-- The comparison and change of Euler coordinates precede the fixed quotient. -/
theorem bufferedMap_eq_comp (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {Q T : X.Modules}
    (e : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ≅ Q)
    (h : Q ⟶ T) :
    bufferedMap X M N q e h =
      (exteriorSumIso X M N q).hom ≫
        Scheme.Modules.exteriorPowerMap (X := X) e.hom (q : ℤ) ≫
          Scheme.Modules.exteriorPowerMap (X := X) h (q : ℤ) := by
  unfold bufferedMap
  rw [Scheme.Modules.exteriorPowerMap_comp]

/-- Any functor carries the two preceding isomorphisms to isomorphisms, so
surjectivity only depends on the actual fixed final quotient. -/
theorem epi_map_bufferedMap {C : Type v} [Category.{w} C]
    (F : X.Modules ⥤ C)
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {Q T : X.Modules}
    (e : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ≅ Q)
    (h : Q ⟶ T)
    [Epi (F.map (Scheme.Modules.exteriorPowerMap (X := X) h (q : ℤ)))] :
    Epi (F.map (bufferedMap X M N q e h)) := by
  letI : IsIso (Scheme.Modules.exteriorPowerMap (X := X) e.hom (q : ℤ)) := inferInstance
  rw [bufferedMap_eq_comp, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  infer_instance

/-- The genuine buffered map is surjective on global sections whenever the
fixed quotient is epi on global sections. -/
theorem bufferedMap_global_surjective
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {Q T : X.Modules}
    (e : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ≅ Q)
    (h : Q ⟶ T)
    [Epi ((Stacks.Cohomology.sectionsFunctor X ⊤).map
      (Scheme.Modules.exteriorPowerMap (X := X) h (q : ℤ)))] :
    Function.Surjective ((bufferedMap X M N q e h).val.app (op ⊤)) := by
  let F := Stacks.Cohomology.sectionsFunctor X ⊤
  letI : Epi (F.map (bufferedMap X M N q e h)) :=
    epi_map_bufferedMap X F M N q e h
  exact (ModuleCat.epi_iff_surjective (F.map (bufferedMap X M N q e h))).mp inferInstance
end NcCubic.Geometry.BufferedExteriorSurjectivity
