module
public import NcCubic.Geometry.CanonicalEulerMiddle
public import NcCubic.Geometry.BiconeComparisonData
public import NcCubic.Geometry.EulerCoordinateAction
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
namespace NcCubic.Geometry.CanonicalEulerMiddle
universe u
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
theorem originalNegativeVertex_cast_projection (A : Type u) [CommRing A] (n : ℕ)
    (j : Fin (n + 1)) :
    (eqToIso (originalNegativeVertex_eq A n)).inv ≫ (originalNegativeBicone A n).π j =
      (biproduct.π (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n) j :
        (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum A n :
          (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules) ⟶
        (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n j :
          (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules)) := by
  rfl

@[simp] theorem positiveLineFactorIso_hom (A : Type u) [CommRing A] (n : ℕ)
    (j : Fin (n + 1)) :
    (positiveLineFactorIso A n j).hom = CanonicalTwistDuality.twistDualMap A n 1 := rfl


/-- The actual canonical middle comparison and its Euler columns, constructed
as one package from the original negative Euler bicone and native positive frame. -/
def positiveEulerMiddleData (A : Type u) [CommRing A] (n : ℕ) :=
  biconeComparisonData (_root_.AlgebraicGeometry.Proj (polyGrading A n))
    (originalNegativeBicone A n)
    (SheafExteriorFrame.coordinateBicone (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
      (twistObj A n 1) (n + 1))
    (originalNegativeBicone_isBilimit A n)
    (SheafExteriorFrame.coordinateBicone_isBilimit (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
      (twistObj A n 1) (n + 1))
    (fun j => positiveLineFactorIso A n j)
    (originalNegativeVertex_eq A n)
    (fun j => (eqToIso (originalNegativeVertex_eq A n)).inv ≫
      (originalNegativeBicone A n).π j)
    (fun _ => rfl)
    (eulerTangentMap A n)
end NcCubic.Geometry.CanonicalEulerMiddle
