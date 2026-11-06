/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Adapted from StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerLineExtension
at pinned Stacks revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache 2.0). -/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace NcCubic.Geometry
universe u

/-- The actual identity comparison between the site and scheme spellings of
sheaves of modules. This retains the underlying sheaf morphisms. -/
def schemeModulesOfSite (X : Scheme.{u}) :
    _root_.SheafOfModules.{u}
      X.ringCatSheaf ⥤ X.Modules where
  obj M := M
  map f := f

/-- The comparison changes only the category spelling and is an equivalence. -/
def schemeModulesOfSiteEquivalence (X : Scheme.{u}) :
    _root_.SheafOfModules.{u}
      X.ringCatSheaf ≌ X.Modules where
  functor := schemeModulesOfSite X
  inverse := { obj M := M, map f := f }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance (X : Scheme.{u}) : (schemeModulesOfSite X).IsEquivalence :=
  (schemeModulesOfSiteEquivalence X).isEquivalence_functor

instance (X : Scheme.{u}) : (schemeModulesOfSite X).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Exact exterior Euler complexes on the site remain short exact in the
scheme category, with the same underlying maps. -/
theorem schemeModulesOfSite_shortExact (X : Scheme.{u})
    (S : ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf)) (hS : S.ShortExact) :
    (S.map (schemeModulesOfSite X)).ShortExact := by
  let := hS.mono_f
  let := hS.epi_g
  exact hS.map (schemeModulesOfSite X)

end NcCubic.Geometry
