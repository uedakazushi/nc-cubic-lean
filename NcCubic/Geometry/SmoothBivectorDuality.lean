/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorRawPairing
public import NcCubic.Geometry.ExteriorDualityCriterion
public import NcCubic.Geometry.ExteriorFunctionalAgreement
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
/-- The actual canonical exterior-duality map for tangent bivectors. -/
def cotangentExteriorDualityMap {X S : Scheme.{u}} (f : X ⟶ S) :
    bivectorSheaf f ⟶ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)) :=
  exteriorDualPairing (Scheme.Hom.relativeDifferentials f)

/-- The generic determinant law has the exact actual tangent/cotangent
form used by bracket comparison. -/
theorem cotangentExteriorDualityMap_unit_of_formula {X S : Scheme.{u}} (f : X ⟶ S)
    (h : HasExteriorDeterminantFormula (Scheme.Hom.relativeDifferentials f)
      (exteriorDualPairing (Scheme.Hom.relativeDifferentials f))) :
    HasUnitDeterminantFormula f (cotangentExteriorDualityMap f) := by
  intro U v a b
  exact h U v ![a,b]

/-- A genuine canonical duality isomorphism. Only the still-to-be-computed
unit law is visible; finite local freeness is the actual sheaf property. -/
def bivectorDualityIsoOfFormula {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials f)]
    (h : HasExteriorDeterminantFormula (Scheme.Hom.relativeDifferentials f)
      (exteriorDualPairing (Scheme.Hom.relativeDifferentials f))) :
    bivectorSheaf f ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)) := by
  have : IsIso (exteriorDualPairing (Scheme.Hom.relativeDifferentials f)) :=
    isIso_of_exteriorDeterminantFormula (Scheme.Hom.relativeDifferentials f) _ h
  exact asIso (exteriorDualPairing (Scheme.Hom.relativeDifferentials f))

theorem bivectorDualityIsoOfFormula_unit {X S : Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials f)]
    (h : HasExteriorDeterminantFormula (Scheme.Hom.relativeDifferentials f)
      (exteriorDualPairing (Scheme.Hom.relativeDifferentials f))) :
    HasUnitDeterminantFormula f (bivectorDualityIsoOfFormula f h).hom :=
  cotangentExteriorDualityMap_unit_of_formula f h

/-- Smoothness supplies actual finite local freeness of the relative cotangent
sheaf; no comparison-isomorphism hypothesis is imposed. -/
def smoothBivectorDualityIsoOfFormula {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (h : HasExteriorDeterminantFormula (Scheme.Hom.relativeDifferentials f)
      (exteriorDualPairing (Scheme.Hom.relativeDifferentials f))) :
    bivectorSheaf f ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)) := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials f) := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  exact bivectorDualityIsoOfFormula f h

theorem smoothBivectorDualityIsoOfFormula_unit {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (h : HasExteriorDeterminantFormula (Scheme.Hom.relativeDifferentials f)
      (exteriorDualPairing (Scheme.Hom.relativeDifferentials f))) :
    HasUnitDeterminantFormula f (smoothBivectorDualityIsoOfFormula f h).hom :=
  cotangentExteriorDualityMap_unit_of_formula f h
end NcCubic.Geometry
