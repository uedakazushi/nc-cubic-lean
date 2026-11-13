module
public import NcCubic.Geometry.ExteriorSiteNativeBridge
public import NcCubic.Geometry.CoordinateTwistFrame
public import NcCubic.Geometry.CoordinateComponentBracket
public import NcCubic.Geometry.ProjectiveExteriorFrame
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ProjPolyChart
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
universe u

/-- A native sheaf morphism on an open set, with the scalar ring fixed before
any projective scheme is instantiated. -/
def nativeSectionLinearMap {X : Scheme.{u}} {M N : X.Modules} (h : M ⟶ N) (U : X.Opens) :
    Γ(M,U) →ₗ[Γ(X,U)] Γ(N,U) := (h.val.app (op U)).hom

variable {n : ℕ}
/-- The original exterior map after the canonical site-to-native exterior-sum comparison. -/
def quadraticExteriorMap {S : Scheme} (f : CanonicalTwistDuality.projective ℂ n ⟶ S)
    (N : ℕ)
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) N ⟶
      tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := S) f) :
    (wedge ℂ n (twistSum ℂ n 1 N) 2 : (CanonicalTwistDuality.projective ℂ n).Modules) ⟶
      Scheme.Modules.exteriorPower (X := CanonicalTwistDuality.projective ℂ n)
        (tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := S) f) 2 :=
  (ExteriorSiteNativeBridge.exteriorSumIso (CanonicalTwistDuality.projective ℂ n)
    (twistObj ℂ n 1) N 2).hom ≫
      Scheme.Modules.exteriorPowerMap (X := CanonicalTwistDuality.projective ℂ n) g 2
end NcCubic.Geometry
