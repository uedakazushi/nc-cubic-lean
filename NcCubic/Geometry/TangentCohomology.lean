/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.TangentTwistEuler
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
/-- Cubic-twisted tangent sheaf has no cohomology in any degree. -/
theorem tangent_cubicTwist_acyclic (n : ℕ) (hn : 3 ≤ n) (q : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).rightDerived q).obj
      ((projectiveTwist ℂ n (-3)).obj (tangentSheaf n))) := by
  let Q := Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤
  let F := projectiveTwist ℂ n (-3)
  let S := (tangentEulerSequence n).map F
  have hS : S.ShortExact :=
    shortExact_map_projectiveTwist ℂ n (-3) (tangentEulerSequence_shortExact n)
  have h₂ : IsZero ((Q.rightDerived q).obj S.X₂) := by
    change IsZero ((Q.rightDerived q).obj (F.obj (tangentEulerSequence n).X₂))
    exact IsZero.of_iso (negative_twistSum_acyclic_native n hn 2 (by omega) (by omega)
      (n + 1) q) ((Q.rightDerived q).mapIso (tangentEulerMiddleTwistIso n))
  have h₁ : IsZero ((Q.rightDerived (q+1)).obj S.X₁) := by
    change IsZero ((Q.rightDerived (q+1)).obj (F.obj (tangentEulerSequence n).X₁))
    exact IsZero.of_iso (negative_twist_acyclic_native n hn 3 (by omega) (by omega) (q+1))
      ((Q.rightDerived (q+1)).mapIso (tangentEulerSourceTwistIso n))
  exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hS Q q h₂ h₁

/-- Degree-one exterior power identification on the source of the bivector Euler sequence. -/
def tangentBivectorEulerSourceIso (n : ℕ) :
    (tangentExteriorEulerSequence n 0).X₁ ≅ tangentSheaf n :=
  tangentExteriorEulerSourceIso n 0 ≪≫
    (_root_.SheafOfModules.algebras _ (tangentSheaf n)).exteriorPowerOneIso

/-- Cubic twist of the bivector Euler middle object is a sum of O(-1). -/
def tangentBivectorEulerMiddleTwistIso (n : ℕ) :
    (projectiveTwist ℂ n (-3)).obj (tangentExteriorEulerSequence n 0).X₂ ≅
      twistSum ℂ n (-1) ((n+1).choose 2) :=
  (projectiveTwist ℂ n (-3)).mapIso (tangentEulerMiddleExteriorIso n 2) ≪≫
    projectiveTwistSumIso ℂ n 2 (-3) ((n+1).choose 2)

/-- The cubic twist of the actual tangent bivector sheaf has no cohomology.
In particular its H0 and H1 vanish, as required by hypersurface restriction. -/
theorem tangentBivector_cubicTwist_acyclic (n : ℕ) (hn : 3 ≤ n) (q : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).rightDerived q).obj
      ((projectiveTwist ℂ n (-3)).obj
        (Scheme.Modules.exteriorPower (tangentSheaf n) (2:ℤ)))) := by
  let Q := Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤
  let F := projectiveTwist ℂ n (-3)
  let S := (tangentExteriorEulerSequence n 0).map F
  have hS : S.ShortExact := shortExact_map_projectiveTwist ℂ n (-3)
    (tangentExteriorEulerSequence_shortExact n 0)
  have h₂ : IsZero ((Q.rightDerived q).obj S.X₂) := by
    change IsZero ((Q.rightDerived q).obj (F.obj (tangentExteriorEulerSequence n 0).X₂))
    exact IsZero.of_iso (negative_twistSum_acyclic_native n hn 1 (by omega) (by omega)
      ((n+1).choose 2) q) ((Q.rightDerived q).mapIso (tangentBivectorEulerMiddleTwistIso n))
  have h₁ : IsZero ((Q.rightDerived (q+1)).obj S.X₁) := by
    change IsZero ((Q.rightDerived (q+1)).obj (F.obj (tangentExteriorEulerSequence n 0).X₁))
    exact IsZero.of_iso (tangent_cubicTwist_acyclic n hn (q+1))
      ((Q.rightDerived (q+1)).mapIso (F.mapIso (tangentBivectorEulerSourceIso n)))
  exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hS Q q h₂ h₁
/-- The same vanishing at the literal Serre-twist spelling used by the
canonical hypersurface restriction sequence. -/
theorem tangentBivector_cubicTwist_raw_acyclic (n : ℕ) (hn : 3 ≤ n) (q : ℕ) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).rightDerived q).obj
      ((Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor (polyGrading ℂ n) (-3)).obj
        (Scheme.Modules.exteriorPower (tangentSheaf n) (2:ℤ)))) :=
  tangentBivector_cubicTwist_acyclic n hn q
/-- Nonnegative twisting-sheaf sums have no higher cohomology. -/
theorem positive_twistSum_acyclic_native (n : ℕ) (hn : 3 ≤ n)
    (d : ℤ) (hd : 0 ≤ d) (s q : ℕ) (hq : 0 < q) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).rightDerived q).obj
      (twistSum ℂ n d s)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  exact isZero_cohomologySheaf_biproduct (twistFamily ℂ (m+1) d s) q
    (fun _ => isZero_cohomologySheaf_twistingSheaf (A := ℂ) (m := m) (by omega) q
      (Or.inr hq))

/-- The actual tangent sheaf has vanishing positive cohomology. -/
theorem tangent_positive_acyclic (n : ℕ) (hn : 3 ≤ n) (q : ℕ) (hq : 0 < q) :
    IsZero (((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).rightDerived q).obj
      (tangentSheaf n)) := by
  let Q := Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤
  let S := tangentEulerSequence n
  have h₂ : IsZero ((Q.rightDerived q).obj S.X₂) :=
    IsZero.of_iso (positive_twistSum_acyclic_native n hn 1 (by omega) (n+1) q hq)
      ((Q.rightDerived q).mapIso (dualEulerMiddleIso ℂ n))
  let eU : S.X₁ ≅ twistObj ℂ n 0 := unitDualIso (ProjectiveAmbient n) ≪≫
    (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading ℂ n)).symm
  have h₁ : IsZero ((Q.rightDerived (q+1)).obj S.X₁) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    have hv : IsZero ((Q.rightDerived (q+1)).obj (twistObj ℂ n 0)) := by
      subst n
      exact isZero_cohomologySheaf_twistingSheaf (A := ℂ) (m := m)
        (by omega) (q+1) (Or.inr (by omega))
    exact IsZero.of_iso hv ((Q.rightDerived (q+1)).mapIso eU)
  exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃
    (tangentEulerSequence_shortExact n) Q q h₂ h₁

/-- The actual Euler quotient on global bivector sections is surjective;
this supplies a genuine quadratic representative for every ambient bivector. -/
theorem epi_bivectorEuler_sections (n : ℕ) (hn : 3 ≤ n) :
    Epi ((Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤).map
      (tangentExteriorEulerSequence n 0).g) := by
  let Q := Stacks.Cohomology.sectionsFunctor (ProjectiveAmbient n) ⊤
  have h₁ : IsZero ((Q.rightDerived 1).obj (tangentExteriorEulerSequence n 0).X₁) :=
    IsZero.of_iso (tangent_positive_acyclic n hn 1 (by omega))
      ((Q.rightDerived 1).mapIso (tangentBivectorEulerSourceIso n))
  exact Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one Q
    (tangentExteriorEulerSequence_shortExact n 0) h₁
end NcCubic.Geometry.ProjectiveCohomology
