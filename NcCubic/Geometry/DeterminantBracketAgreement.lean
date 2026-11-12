/- A literal determinant pairing evaluates to the actual bivector bracket. -/
module
public import NcCubic.Geometry.ExteriorPairingPullback
public import NcCubic.Geometry.ExteriorFunctionalAgreement
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
variable {X S : Scheme.{u}} (f : X ⟶ S)
def curriedDeterminantMap
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf) :
    bivectorSheaf f ⟶ dualSheaf (exteriorSquare X (Scheme.Hom.relativeDifferentials f)) :=
  SheafTensorCurry.tensorHomEquiv X.toRingedSpace _ _ _ q

lemma curriedDeterminantMap_hasUnitFormula
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials f) q) :
    HasUnitDeterminantFormula f (curriedDeterminantMap f q) := by
  intro U v a b
  have hc := SheafTensorCurry.tensorHomEquiv_isTensorCurry X.toRingedSpace q U
    (exteriorWedgeAlternating (tangentSheaf f) U v) (cotangentWedgeSection f U ![a,b])
  exact hc.trans (hq U v ![a,b])

lemma determinantPairing_bracket
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials f) q)
    (U : X.Opens) (pi : Γ(bivectorSheaf f,U)) (a b : Γ(X,U)) :
    q.val.app (op U) (PullbackDual.tensorSheafPure X _ _ U
      (pi ⊗ₜ[X.presheaf.obj (op U)] exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials f) U
        ![(Scheme.Hom.universalRelativeDerivation f).d a,(Scheme.Hom.universalRelativeDerivation f).d b])) =
      bivectorSectionBracket f U pi a b := by
  have hc := SheafTensorCurry.tensorHomEquiv_isTensorCurry X.toRingedSpace q U pi
    (cotangentWedgeSection f U
      ![(Scheme.Hom.universalRelativeDerivation f).d a,(Scheme.Hom.universalRelativeDerivation f).d b])
  exact hc.symm.trans (unitDeterminant_eval_arbitrary f (curriedDeterminantMap f q)
    (curriedDeterminantMap_hasUnitFormula f q hq) U pi a b)
end NcCubic.Geometry.ImmersionBracketNaturality
