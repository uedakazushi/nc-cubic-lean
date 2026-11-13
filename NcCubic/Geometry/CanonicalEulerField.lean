/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.CanonicalTwistDuality
public import NcCubic.Geometry.CanonicalEulerMiddle
public import NcCubic.Geometry.EulerCoordinateAction
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.TensorStalkRingedSpace
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
/-- The canonical coordinate Euler field: use actual twist multiplication to
identify the positive line with the dual negative line, then the original Euler quotient. -/
def canonicalEulerField (j : Fin (n+1)) :
    (CanonicalTwistDuality.twist R n 1 : (AlgebraicGeometry.Proj (polyGrading R n)).Modules) ⟶
      tangentSheaf (X := AlgebraicGeometry.Proj (polyGrading R n))
      (S := Spec (CommRingCat.of R)) (projToSpecCoeff R n) :=
  (CanonicalEulerMiddle.positiveLineFactorIso R n j).hom ≫ eulerTangentColumn R n j

/-- Coordinate Euler fields pair the positive coefficient with the actual
twisted partial derivative through the literal multiplication pairing. -/
theorem canonicalEulerField_action
    (U : (CanonicalTwistDuality.projective R n).Opens) (j : Fin (n+1))
    (s : (CanonicalTwistDuality.twist R n 1).val.obj (op U))
    (a : Γ(CanonicalTwistDuality.projective R n,U)) :
    tangentSectionDerivation (projToSpecCoeff R n) U
      (Scheme.Modules.Hom.app (canonicalEulerField R n j) U s) a =
      (CanonicalTwistDuality.twistPairing R n 1).val.app (op U)
        (toTensorSheafSection (CanonicalTwistDuality.projective R n).toRingedSpace
          (CanonicalTwistDuality.twist R n 1) (CanonicalTwistDuality.twist R n (-1))
          (op U) (s ⊗ₜ[(CanonicalTwistDuality.projective R n).presheaf.obj (op U)]
            (pderivApp R n j U a))) := by
  have hκ : (CanonicalEulerMiddle.positiveLineFactorIso R n j).hom =
      CanonicalTwistDuality.twistDualMap R n 1 := rfl
  dsimp only [canonicalEulerField]
  rw [hκ]
  exact (eulerTangentColumn_action R n U j
    (Scheme.Modules.Hom.app (CanonicalTwistDuality.twistDualMap R n 1) U s) a).trans
    (CanonicalTwistDuality.twistDualMap_isTensorCurry R n 1 U s (pderivApp R n j U a))
end NcCubic.Geometry
