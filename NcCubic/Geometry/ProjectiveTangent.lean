/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Actual complex-projective tangent sheaf and the dual Euler sequence. -/
module
public import NcCubic.Geometry.ProjectiveCotangentRank
public import NcCubic.Geometry.ModulesBridge
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Extension
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
open AlgebraicGeometry CategoryTheory
namespace NcCubic.Geometry.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ProjEulerSequence
open NcCubic.Geometry.CotangentCoordinates

/-- The actual tangent sheaf on complex projective `n`-space. -/
abbrev tangentSheaf (n : ℕ) : (ProjectiveAmbient n).Modules :=
  dualSheaf (X := ProjectiveAmbient n)
    (Scheme.Hom.relativeDifferentials (ambientProjection n))

/-- Tangent rank follows from actual polynomial chart bases and sheaf duality. -/
theorem tangentSheaf_locallyFreeOfRank (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := (ProjectiveAmbient n).ringCatSheaf) (tangentSheaf n) n :=
  isFiniteLocallyFreeOfRank_dualSheaf (X := ProjectiveAmbient n) _ n
    (projectiveCotangent_locallyFreeOfRank n)

/-- The genuine cotangent Euler sequence dualizes to an actual tangent Euler
sequence. All finite local freeness is proved from charts and exactness. -/
theorem dual_euler_shortExact (n : ℕ) :
    ∃ (w : dualMap (X := ProjectiveAmbient n) (eulerSurjection ℂ n) ≫
        dualMap (X := ProjectiveAmbient n) (eulerFirstArrow ℂ n) = 0),
      (ShortComplex.mk (dualMap (X := ProjectiveAmbient n) (eulerSurjection ℂ n))
        (dualMap (X := ProjectiveAmbient n) (eulerFirstArrow ℂ n)) w).ShortExact := by
  let X := ProjectiveAmbient n
  let S₀ : ShortComplex (_root_.SheafOfModules X.ringCatSheaf) := ShortComplex.mk
    (eulerFirstArrow ℂ n) (eulerSurjection ℂ n)
    (eulerFirstArrow_comp_eulerSurjection ℂ n)
  let S := S₀.map (schemeModulesOfSite X)
  have hs : S.ShortExact := schemeModulesOfSite_shortExact X S₀ (shortExact_eulerSequence ℂ n)
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) S.X₁ n := projectiveCotangent_locallyFreeOfRank n
  let : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) S.X₃ 1 :=
    Stacks.AlgebraicGeometry.ProjTwistRank.isFiniteLocallyFreeOfRank_unit ℂ n
  have hE := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (R := X.ringCatSheaf) S.X₁ n
  have hG := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (R := X.ringCatSheaf) S.X₃ 1
  have hF := Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact S hs hE hG
  exact exists_dualSheaf_shortExact (X := X) S.f S.g S.zero hs.mono_f hs.epi_g hs.exact hE hF hG

end NcCubic.Geometry.ProjectiveCohomology
