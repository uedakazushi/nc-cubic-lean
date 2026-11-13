/- The actual canonical exterior pairing has the literal determinant value. -/
module
public import NcCubic.Geometry.CanonicalDeterminantPairing
public import NcCubic.Geometry.ExteriorRawPairingWedge
public import NcCubic.Geometry.ExteriorRawDualEvaluation
public import NcCubic.Geometry.ExteriorRawPairingEvaluation
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
lemma canonicalDeterminantPairing_hasDeterminantFormula_of_toRaw {X : Scheme.{u}} (M : X.Modules)
    (hRaw : ∀ (U : X.Opens) (v : Fin 2 → Γ(dualSheaf M,U)),
      (exteriorDualToRaw M).val.app (op U)
        ((exteriorDualPairing M).val.app (op U) (exteriorWedgeAlternating (dualSheaf M) U v)) =
      localRawExteriorPairing M (v 0) (v 1)) :
    HasDeterminantFormula M (canonicalDeterminantPairing M) := by
  apply scalarPairingOfMap_hasDeterminantFormula
  intro U v w
  have hb := exteriorDualToRaw_eval_native_wedge M U
    ((exteriorDualPairing M).val.app (op U) (exteriorWedgeAlternating (dualSheaf M) U v)) w
  have hr := congrArg (fun l : Γ(exteriorRawDualSheaf M,U) =>
    (l.app (op (Over.mk (𝟙 U)))).hom
      (exteriorRawWedge M U (fun j => (siteSectionSemilinearEquiv M U).symm (w j)))) (hRaw U v)
  exact hb.trans (hr.trans (localRawExteriorPairing_eval_wedge M U (v 0) (v 1) w))
lemma canonicalDeterminantPairing_hasDeterminantFormula {X : Scheme.{u}} (M : X.Modules) :
    HasDeterminantFormula M (canonicalDeterminantPairing M) :=
  canonicalDeterminantPairing_hasDeterminantFormula_of_toRaw M
    (fun U v => exteriorDualPairing_toRaw_native_wedge M U v)
end NcCubic.Geometry.ImmersionBracketNaturality
