/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Canonical differential and exterior push of genuine tangent bivector sections.
-/
module
public import NcCubic.Geometry.PullbackDual
public import NcCubic.Geometry.ImmersionCotangent
public import NcCubic.Geometry.ImmersionExterior
public import NcCubic.Geometry.ProjectiveBivector
public import NcCubic.Geometry.ProjectiveCotangentRank
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
@[expose] public section
universe u
namespace NcCubic.Geometry.ImmersionBivector
noncomputable section
open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X P S : Scheme.{u}}

/-- The canonical dual base-change isomorphism, justified by finite local
freeness rather than assumed as comparison data. -/
def ambientDualPullbackIso (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) :
    (Scheme.Modules.pullback i).obj (dualSheaf (Scheme.Hom.relativeDifferentials p)) ≅
      dualSheaf ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) :=
  @asIso _ _ _ _ (PullbackDual.pullbackDualMap i (Scheme.Hom.relativeDifferentials p))
    (PullbackDual.pullbackDualMap_isIso i (Scheme.Hom.relativeDifferentials p) hΩ)

/-- Tangent vectors map to the pullback of ambient tangent vectors by
transposing the cotangent map. -/
def tangentMap (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) :
    dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p)) ⟶
      (Scheme.Modules.pullback i).obj (dualSheaf (Scheme.Hom.relativeDifferentials p)) :=
  dualMap (cotangentMap i p) ≫ (ambientDualPullbackIso i p hΩ).inv

/-- The tangent map agrees with the actual transpose of the differential. -/
theorem tangentMap_comp_dualComparison (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) :
    tangentMap i p hΩ ≫ (ambientDualPullbackIso i p hΩ).hom = dualMap (cotangentMap i p) := by
  simp [tangentMap, Category.assoc]

/-- Evaluation of the pushed tangent section on an ambient differential is
precomposition by the actual cotangent map. -/
theorem tangentMap_pairing (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) (U : X.Opens)
    (t : Γ(dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p)), U))
    (W : CategoryTheory.Over U)
    (ω : Γ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p), W.left)) :
    dualPairing ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p))
      (Scheme.Modules.Hom.app (ambientDualPullbackIso i p hΩ).hom U
        (Scheme.Modules.Hom.app (tangentMap i p hΩ) U t)) W ω =
      dualPairing (Scheme.Hom.relativeDifferentials (i ≫ p)) t W
        (Scheme.Modules.Hom.app (cotangentMap i p) W.left ω) := by
  have hs : Scheme.Modules.Hom.app (ambientDualPullbackIso i p hΩ).hom U
        (Scheme.Modules.Hom.app (tangentMap i p hΩ) U t) =
      Scheme.Modules.Hom.app (dualMap (cotangentMap i p)) U t := by
    change Scheme.Modules.Hom.app
      (tangentMap i p hΩ ≫ (ambientDualPullbackIso i p hΩ).hom) U t = _
    rw [tangentMap_comp_dualComparison]
  rw [hs]
  exact dualPairing_dualMap (cotangentMap i p) t W ω

/-- The same canonical differential map on every exterior degree, including
trivectors needed for the Jacobiator comparison. -/
def multivectorMap (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) (n : ℤ) :
    Scheme.Modules.exteriorPower (dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p))) n ⟶
      (Scheme.Modules.pullback i).obj
        (Scheme.Modules.exteriorPower (dualSheaf (Scheme.Hom.relativeDifferentials p)) n) :=
  exteriorAlongPullback i (tangentMap i p hΩ) n

/-- Canonical image of a bivector in the pullback of the ambient bivector
bundle. This specializes to every smooth hypersurface immersion. -/
def bivectorMap (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) :
    Scheme.Modules.exteriorPower (dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p))) 2 ⟶
      (Scheme.Modules.pullback i).obj
        (Scheme.Modules.exteriorPower (dualSheaf (Scheme.Hom.relativeDifferentials p)) 2) :=
  multivectorMap i p hΩ 2

/-- The bivector map is exactly the second exterior power of the tangent map,
through the canonical pullback comparison. -/
theorem bivectorMap_comp_exteriorComparison (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) :
    bivectorMap i p hΩ ≫ (exteriorPullbackIso i
      (dualSheaf (Scheme.Hom.relativeDifferentials p)) 2).hom =
      Scheme.Modules.exteriorPowerMap (tangentMap i p hΩ) 2 := by
  simp [bivectorMap, multivectorMap, exteriorAlongPullback, Category.assoc]

/-- Image of an actual local bivector section under the immersion map. -/
def imageSection (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) (U : X.Opens)
    (π : (Scheme.Modules.exteriorPower
      (dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p))) 2).val.obj (.op U)) :=
  (bivectorMap i p hΩ).val.app (.op U) π

/-- The actual bivector image commutes with restriction to every smaller open. -/
theorem imageSection_restrict (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p)) (U V : X.Opens) (h : U ≤ V)
    (π : (Scheme.Modules.exteriorPower
      (dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p))) 2).val.obj (.op V)) :
    imageSection i p hΩ U ((Scheme.Modules.exteriorPower
      (dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p))) 2).val.map
        (homOfLE h).op π) =
      ((Scheme.Modules.pullback i).obj (Scheme.Modules.exteriorPower
        (dualSheaf (Scheme.Hom.relativeDifferentials p)) 2)).val.map (homOfLE h).op
          (imageSection i p hΩ V π) :=
  PresheafOfModules.naturality_apply (bivectorMap i p hΩ).val (homOfLE h).op π

end
end NcCubic.Geometry.ImmersionBivector

namespace NcCubic.Geometry.ImmersionBivector
noncomputable section
open AlgebraicGeometry CategoryTheory

/-- The genuine projective ambient case. Cotangent local freeness is proved
from explicit polynomial charts, with no extra hypothesis from the caller. -/
def projectiveBivectorMap {n : ℕ} {Y : Scheme.{0}}
    (i : Y ⟶ ProjectiveAmbient n) :
    bivectorSheaf (i ≫ CotangentCoordinates.ambientProjection n) ⟶
      (Scheme.Modules.pullback i).obj
        (bivectorSheaf (CotangentCoordinates.ambientProjection n)) :=
  bivectorMap i (CotangentCoordinates.ambientProjection n)
    (CotangentCoordinates.projectiveCotangent_locallyFreeOfRank n).isFiniteLocallyFree

/-- Canonical image of an actual global bivector section in the pullback
of the ambient projective bivector bundle. -/
def projectiveImageSection {n : ℕ} {Y : Scheme.{0}}
    (i : Y ⟶ ProjectiveAmbient n)
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    Γ((Scheme.Modules.pullback i).obj
      (bivectorSheaf (CotangentCoordinates.ambientProjection n)), ⊤) :=
  (projectiveBivectorMap i).val.app (.op ⊤) π

end
end NcCubic.Geometry.ImmersionBivector
