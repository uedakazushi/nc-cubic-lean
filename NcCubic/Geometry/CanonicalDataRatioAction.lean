module
public import NcCubic.Geometry.CanonicalEulerLiteralData
public import NcCubic.Geometry.ColumnScalarAction
public import NcCubic.Geometry.ProjectiveCotangentRank
public import NcCubic.Geometry.QuadraticComponentEvaluation
public import NcCubic.Geometry.CanonicalEulerScalarColumn
public import NcCubic.Geometry.CanonicalQuadraticRatioBracket
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace NcCubic.Geometry.CanonicalEulerMiddle
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra

def literalColumnScalarNative (n : ℕ)
    (U : (_root_.AlgebraicGeometry.Proj (polyGrading ℂ n)).Opens)
    (j : Fin (n + 1)) (s : (twistObj ℂ n 1).val.obj (op U))
    (a : Γ(_root_.AlgebraicGeometry.Proj (polyGrading ℂ n), U)) :=
  BiconeComparisonData.column_scalar_action_source
    (X := _root_.AlgebraicGeometry.Proj (polyGrading ℂ n))
    (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n)
    (positiveEulerMiddleLiteralData ℂ n) U j
    (nativeFrameColumn (X := _root_.AlgebraicGeometry.Proj (polyGrading ℂ n))
      (twistObj ℂ n 1) (n + 1) j)
    (by exact SheafExteriorFrame.coordinateBicone_ι (twistObj ℂ n 1) (n + 1) j)
    s a
theorem literalData_hasCanonicalRatioAction (n : ℕ) :
    HasCanonicalRatioAction
      ((positiveEulerMiddleLiteralData ℂ n).iso.hom ≫ eulerTangentMap ℂ n) := by
  intro i j l U hU
  exact (literalColumnScalarNative n U j
    (CoordinateTwistFrame.frameOne i U hU)
    (CanonicalEulerCoordinateEvaluation.restrictedRatio i l U hU)).trans
    ((canonicalLineFactor_eulerColumn_action n j U
      (CoordinateTwistFrame.frameOne i U hU)
      (CanonicalEulerCoordinateEvaluation.restrictedRatio i l U hU)).trans
      (CanonicalEulerCoordinateEvaluation.canonicalEulerField_frame_ratio i l j U hU))
end NcCubic.Geometry.CanonicalEulerMiddle
