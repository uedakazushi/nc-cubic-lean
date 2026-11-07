/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local adapters; upstream constructions retain their licenses. -/
module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic

set_option maxHeartbeats 1000000
@[expose] public noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory AlgebraicGeometry
namespace NcCubic.Geometry.ProjectiveCohomology
universe u
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ReflexiveModules

/-- The negative Serre twist is the actual sheaf dual of the positive twist.
The comparison comes from multiplication of twisting sheaves and uniqueness of
an invertible sheaf's tensor inverse. -/
def twistNegIsoDual (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-d) ≅
      dualSheaf (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
        (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d) := by
  let X : Scheme.{u} := _root_.AlgebraicGeometry.Proj (polyGrading A n)
  let L : X.Modules := ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d
  let M : X.Modules := ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) (-d)
  let e₀ : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj M ≅
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) 0 := by
    simpa only [add_neg_cancel] using tensorTwistingSheafIso A n d (-d)
  let e := e₀ ≪≫
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading A n)
  exact Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L M e

end NcCubic.Geometry.ProjectiveCohomology
