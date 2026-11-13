module
public import NcCubic.Geometry.CanonicalEulerFrame
public import NcCubic.Geometry.DualIsoTransport
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

/-- The canonical multiplication-curry factor in each Euler coordinate. -/
def positiveLineFactorIso (A : Type u) [CommRing A] (n : ℕ) (j : Fin (n + 1)) :
    (twistObj A n 1 : (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules) ≅
      dualSheaf (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
        ((schemeModulesOfSite (_root_.AlgebraicGeometry.Proj (polyGrading A n))).obj
          (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n j)) :=
  CanonicalTwistDuality.twistDualIso A n 1

/-- Canonical comparison at the literal native coefficient-frame vertices. -/
def nativeBiconeMiddleIso (A : Type u) [CommRing A] (n : ℕ) :=
  dualBiconeComparisonIso (_root_.AlgebraicGeometry.Proj (polyGrading A n))
    (originalNegativeBicone A n)
    (SheafExteriorFrame.coordinateBicone (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
      (twistObj A n 1) (n + 1))
    (originalNegativeBicone_isBilimit A n)
    (SheafExteriorFrame.coordinateBicone_isBilimit (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
      (twistObj A n 1) (n + 1))
    (fun j => positiveLineFactorIso A n j)

end NcCubic.Geometry.CanonicalEulerMiddle

namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
universe u

/-- Isolate source-vertex normalization as an ordinary object equality. -/
theorem nativePositiveVertex_eq (A : Type u) [CommRing A] (n : ℕ) :
    (SheafExteriorFrame.coordinateBicone (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
      (twistObj A n 1) (n + 1)).pt =
      (twistSum A n 1 (n + 1) : (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules) := rfl

/-- Isolate target-vertex normalization BEFORE applying the large dual-sheaf functor. -/
theorem originalNegativeVertex_eq (A : Type u) [CommRing A] (n : ℕ) :
    (originalNegativeBicone A n).pt =
      (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum A n :
        (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules) := rfl


/-- Canonical positive coordinate frame to the dual ORIGINAL Euler bundle. -/
def positiveEulerMiddleIso (A : Type u) [CommRing A] (n : ℕ) :
    (twistSum A n 1 (n + 1) : (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules) ≅
      dualSheaf (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
        (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum A n) :=
  dualIsoChangeTarget (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
    (nativeBiconeMiddleIso A n) (originalNegativeVertex_eq A n)


end NcCubic.Geometry.CanonicalEulerMiddle
