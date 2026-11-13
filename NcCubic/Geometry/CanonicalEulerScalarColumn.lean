module
public import NcCubic.Geometry.CanonicalEulerField
public import NcCubic.Geometry.ProjectiveCotangentRank
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ProjEulerSequence
namespace NcCubic.Geometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
private theorem tangentDerivation_comp_apply {X S : Scheme.{u}} (f : X ⟶ S)
    {L M : X.Modules} (h : L ⟶ M)
    (k : M ⟶ tangentSheaf (X := X) (S := S) f) (U : X.Opens)
    (s : Γ(L,U)) (a : Γ(X,U)) :
    tangentSectionDerivation (X := X) (S := S) f U
      (k.val.app (op U) (h.val.app (op U) s)) a =
    tangentSectionDerivation (X := X) (S := S) f U
      ((h ≫ k).val.app (op U) s) a := rfl

theorem canonicalLineFactor_eulerColumn_action (n : ℕ) (j : Fin (n+1))
    (U : (CanonicalTwistDuality.projective ℂ n).Opens)
    (s : (twistObj ℂ n 1).val.obj (op U))
    (a : Γ(CanonicalTwistDuality.projective ℂ n,U)) :
    tangentSectionDerivation (X := CanonicalTwistDuality.projective ℂ n)
      (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      (((dualMap (X := CanonicalTwistDuality.projective ℂ n)
          (biproduct.π (twistMinusOneFamily ℂ n) j) ≫ eulerTangentMap ℂ n).val.app (op U))
        ((CanonicalEulerMiddle.positiveLineFactorIso ℂ n j).hom.val.app (op U) s)) a =
    tangentSectionDerivation (X := CanonicalTwistDuality.projective ℂ n)
      (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      ((canonicalEulerField ℂ n j).val.app (op U) s) a := by
  exact tangentDerivation_comp_apply (X := CanonicalTwistDuality.projective ℂ n)
    (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n)
    (CanonicalEulerMiddle.positiveLineFactorIso ℂ n j).hom
    (eulerTangentColumn ℂ n j) U s a
end NcCubic.Geometry
