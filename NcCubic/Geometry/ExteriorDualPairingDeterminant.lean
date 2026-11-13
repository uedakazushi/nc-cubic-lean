module
public import NcCubic.Geometry.ExteriorRawPairingWedge
public import NcCubic.Geometry.ExteriorRawDualEvaluation
public import NcCubic.Geometry.ExteriorRawPairingEvaluation
public import NcCubic.Geometry.ExteriorDualityCriterion
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem exteriorDualPairing_hasDeterminantFormula {X : Scheme.{u}} (M : X.Modules) :
    HasExteriorDeterminantFormula M (exteriorDualPairing M) := by
  intro U lam v
  let x := (exteriorDualPairing M).app U (exteriorWedgeAlternating (dualSheaf M) U lam)
  have hn := exteriorDualPairing_toRaw_native_wedge M U lam
  have hr := (nativeModuleHom_app_apply (exteriorDualToRaw M) U x).symm.trans hn
  have he := congrArg (fun r : Γ(exteriorRawDualSheaf M,U) =>
      (r.app (op (Over.mk (𝟙 U)))).hom (exteriorRawWedge M U
        (fun i => (siteSectionSemilinearEquiv M U).symm (v i)))) hr
  exact (exteriorDualToRaw_eval_native_wedge M U x v).trans
    (he.trans (localRawExteriorPairing_eval_wedge M U (lam 0) (lam 1) v))

set_option backward.isDefEq.respectTransparency false in
instance exteriorDualPairing_isIso {X : Scheme.{u}} (M : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M] :
    IsIso (exteriorDualPairing M) :=
  isIso_of_exteriorDeterminantFormula M (exteriorDualPairing M)
    (exteriorDualPairing_hasDeterminantFormula M)
end NcCubic.Geometry
