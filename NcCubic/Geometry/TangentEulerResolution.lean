/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Canonical tangent Euler complexes on actual complex projective space. -/
module
public import NcCubic.Geometry.ProjectiveTangent
public import NcCubic.Geometry.LineExteriorEuler
public import NcCubic.Geometry.ProjectiveTwistInverse
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.UnitDual
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
open AlgebraicGeometry CategoryTheory
namespace NcCubic.Geometry.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ProjEulerSequence

/-- The actual dual Euler complex. Only its zero-composition proof is selected;
its two morphisms are the fixed duals of the genuine cotangent Euler arrows. -/
def tangentEulerSequence (n : ℕ) : ShortComplex (ProjectiveAmbient n).Modules :=
  ShortComplex.mk (dualMap (X := ProjectiveAmbient n) (eulerSurjection ℂ n))
    (dualMap (X := ProjectiveAmbient n) (eulerFirstArrow ℂ n))
    (dual_euler_shortExact n).choose

theorem tangentEulerSequence_shortExact (n : ℕ) : (tangentEulerSequence n).ShortExact :=
  (dual_euler_shortExact n).choose_spec

instance (n : ℕ) : Mono (tangentEulerSequence n).f :=
  (tangentEulerSequence_shortExact n).mono_f
instance (n : ℕ) : Epi (tangentEulerSequence n).g :=
  (tangentEulerSequence_shortExact n).epi_g
instance (n : ℕ) : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
    (R := (ProjectiveAmbient n).ringCatSheaf) (tangentEulerSequence n).X₁ 1 :=
  isFiniteLocallyFreeOfRank_dualSheaf (X := ProjectiveAmbient n)
    (_root_.SheafOfModules.unit (ProjectiveAmbient n).ringCatSheaf) 1
    (Stacks.AlgebraicGeometry.ProjTwistRank.isFiniteLocallyFreeOfRank_unit ℂ n)
instance (n : ℕ) : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
    (R := (ProjectiveAmbient n).ringCatSheaf) (tangentEulerSequence n).X₃ n :=
  tangentSheaf_locallyFreeOfRank n

/-- The canonical exterior tangent Euler sequence. Its quotient map remains
exactly the exterior power of the actual tangent Euler quotient. -/
def tangentExteriorEulerSequence (n k : ℕ) : ShortComplex (ProjectiveAmbient n).Modules :=
  wedgeLineComplex (tangentEulerSequence n).f (tangentEulerSequence n).g
    (tangentEulerSequence n).zero (tangentEulerSequence_shortExact n).exact n k

theorem tangentExteriorEulerSequence_shortExact (n k : ℕ) :
    (tangentExteriorEulerSequence n k).ShortExact :=
  wedgeLineComplex_shortExact (tangentEulerSequence n).f (tangentEulerSequence n).g
    (tangentEulerSequence n).zero (tangentEulerSequence_shortExact n).exact n k

@[simp] theorem tangentExteriorEulerSequence_g (n k : ℕ) :
    (tangentExteriorEulerSequence n k).g =
      Scheme.Modules.exteriorPowerMap (tangentEulerSequence n).g ((1 + (k + 1) : ℕ) : ℤ) := rfl

/-- The first object is the preceding tangent exterior power, through the
actual dual-unit and tensor-unit identifications. -/
def tangentExteriorEulerSourceIso (n k : ℕ) :
    (tangentExteriorEulerSequence n k).X₁ ≅
      Scheme.Modules.exteriorPower (tangentSheaf n) ((k + 1 : ℕ) : ℤ) := by
  let P := ProjectiveAmbient n
  let S := tangentEulerSequence n
  let Q := Scheme.Modules.exteriorPower (tangentSheaf n) ((k + 1 : ℕ) : ℤ)
  let eU : S.X₁ ≅ _root_.SheafOfModules.unit P.ringCatSheaf := unitDualIso P
  exact wedgeLineComplex_sourceIso S.f S.g S.zero
      (tangentEulerSequence_shortExact n).exact n k ≪≫
    (Functor.mapIso (Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf) eU).app Q ≪≫
    Stacks.AlgebraicGeometry.ProjTwistRank.unitTensorModuleIso ℂ n Q

/-- Every tangent exterior power is an actual finite locally free sheaf,
with the binomial rank supplied by the proved tangent rank. -/
theorem tangentExterior_locallyFreeOfRank (n p : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (ProjectiveAmbient n).ringCatSheaf)
      (Scheme.Modules.exteriorPower (tangentSheaf n) (p : ℤ)) (n.choose p) := by
  let := tangentSheaf_locallyFreeOfRank n
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (tangentSheaf n) n p

theorem tangentExterior_locallyFree (n p : ℕ) :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree
      (R := (ProjectiveAmbient n).ringCatSheaf)
      (Scheme.Modules.exteriorPower (tangentSheaf n) (p : ℤ)) := by
  let := tangentExterior_locallyFreeOfRank n p
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (Scheme.Modules.exteriorPower (tangentSheaf n) (p : ℤ)) (n.choose p)

end NcCubic.Geometry.ProjectiveCohomology
