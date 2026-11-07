/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ProjectiveCohomology
public import NcCubic.Geometry.TangentEulerResolution
public import NcCubic.Geometry.PositiveTwistExterior
public import NcCubic.Geometry.ProjectiveTwistDual
public import NcCubic.Geometry.ProjectiveTwistExact
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
namespace NcCubic.Geometry.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ReflexiveModules
/-- Negative twisting-sheaf sums, in the native dimension convention. -/
theorem negative_twistSum_acyclic_native (n : ℕ) (hn : 3 ≤ n)
    (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) (s q : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).rightDerived q).obj
      (twistSum ℂ n (-(r : ℤ)) s)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  exact negative_twistSum_acyclic ℂ m hn r hr hr' s q

/-- Exterior powers of the actual middle tangent Euler object have the
positive Serre-twist decomposition. The Euler quotient arrow is unchanged. -/
def tangentEulerMiddleExteriorIso (n p : ℕ) :
    Scheme.Modules.exteriorPower (tangentEulerSequence n).X₂ (p : ℤ) ≅
      twistSum ℂ n (p : ℤ) ((n + 1).choose p) :=
  wedgeMapIso ℂ n (dualEulerMiddleIso ℂ n) p ≪≫
    positiveTwistSumExteriorIso ℂ n n p

/-- Cubic twist of the first Euler object is the actual negative line bundle. -/
def tangentEulerSourceTwistIso (n : ℕ) :
    (projectiveTwist ℂ n (-3)).obj (tangentEulerSequence n).X₁ ≅ twistObj ℂ n (-3) :=
  (projectiveTwist ℂ n (-3)).mapIso (unitDualIso (ProjectiveAmbient n)) ≪≫
    unitTensorModuleIso ℂ n (twistObj ℂ n (-3))

/-- Cubic twist of the middle Euler object is a sum of O(-2). -/
def tangentEulerMiddleTwistIso (n : ℕ) :
    (projectiveTwist ℂ n (-3)).obj (tangentEulerSequence n).X₂ ≅
      twistSum ℂ n (-2) (n + 1) :=
  (projectiveTwist ℂ n (-3)).mapIso (dualEulerMiddleIso ℂ n) ≪≫
    projectiveTwistSumIso ℂ n 1 (-3) (n + 1)
/-- Negative line bundles, with projective dimension n. -/
theorem negative_twist_acyclic_native (n : ℕ) (hn : 3 ≤ n)
    (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 3) (q : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).rightDerived q).obj
      (twistObj ℂ n (-(r : ℤ)))) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  exact negative_twist_acyclic ℂ m hn r hr hr' q

end NcCubic.Geometry.ProjectiveCohomology
