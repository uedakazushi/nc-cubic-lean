module
public import NcCubic.Geometry.CanonicalEulerField
public import NcCubic.Geometry.ProjectiveCoordinateDerivatives
public import StacksFrontier.AlgebraicGeometry.ProjTrivialization.PowerSection
@[expose] public noncomputable section
namespace NcCubic.Geometry.CoordinateTwistFrame
open AlgebraicGeometry Opposite MvPolynomial CategoryTheory
open scoped TensorProduct
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj
attribute [local instance] MvPolynomial.gradedAlgebra ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}
abbrev ambient := AlgebraicGeometry.Proj (polyGrading ℂ n)
local instance (x : ProjectiveSpectrum.top (polyGrading ℂ n)) : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
abbrev chart (i : Fin (n+1)) := ProjectiveSpectrum.basicOpen (polyGrading ℂ n) (X i)
/-- The coordinate section that freely generates O(1) on any subopen of its standard chart. -/
def frameOne (i : Fin (n+1)) (U : (ambient (n:=n)).Opens) (hU : U ≤ chart i) :
    Γ((CanonicalTwistDuality.twist ℂ n 1 : (ambient (n:=n)).Modules),U) :=
  powSection (polyGrading ℂ n) (isHomogeneous_X ℂ i) 1 hU
/-- Its quadratic power freely generates O(2) on the same subopens. -/
def frameTwo (i : Fin (n+1)) (U : (ambient (n:=n)).Opens) (hU : U ≤ chart i) :
    Γ((CanonicalTwistDuality.twist ℂ n 2 : (ambient (n:=n)).Modules),U) :=
  powSection (polyGrading ℂ n) (isHomogeneous_X ℂ i) 2 hU

theorem exists_smul_frameTwo (i : Fin (n+1)) (U : (ambient (n:=n)).Opens)
    (hU : U ≤ chart i) (s : Γ((CanonicalTwistDuality.twist ℂ n 2 : (ambient (n:=n)).Modules),U)) :
    ∃ r : Γ(ambient (n:=n),U), r • frameTwo i U hU = s :=
  (existsUnique_smul_powSection (polyGrading ℂ n) (isHomogeneous_X ℂ i) 2 hU s).exists

theorem frameOne_val (i : Fin (n+1)) (U : (ambient (n:=n)).Opens)
    (hU : U ≤ chart i) (x : U) :
    (frameOne i U hU).1 x = LocalizedModule.mk (X i : CubicPolynomial (n+1))
      (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
  change LocalizedModule.mk ((X i : CubicPolynomial (n+1)) ^ 1) _ = _
  simp only [pow_one]

theorem frameTwo_val (i : Fin (n+1)) (U : (ambient (n:=n)).Opens)
    (hU : U ≤ chart i) (x : U) :
    (frameTwo i U hU).1 x = LocalizedModule.mk ((X i : CubicPolynomial (n+1))^2)
      (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) := rfl
theorem frameTwo_eq_product (i : Fin (n+1)) (U : (ambient (n:=n)).Opens)
    (hU : U ≤ chart i) :
    (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
      (polyGrading ℂ n) 1 1).val.app (op U)
      (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
        (ambient (n:=n)).toRingedSpace
        (CanonicalTwistDuality.twist ℂ n 1) (CanonicalTwistDuality.twist ℂ n 1)
        (op U) (frameOne i U hU ⊗ₜ[_] frameOne i U hU)) = frameTwo i U hU := by
  apply Subtype.ext
  funext x
  rw [Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul,
    frameOne_val, frameTwo_val]
  simpa only [one_mul, pow_two] using
    (LocalizedModule.mk_mul_mk (a₁ := (X i : CubicPolynomial (n+1)))
      (a₂ := (X i : CubicPolynomial (n+1)))
      (s₁ := (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl))
      (s₂ := (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)))
end NcCubic.Geometry.CoordinateTwistFrame
