/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Focused adaptation of the twist equivalence in pinned Stacks
ProjectiveSpaceHodgeCohomology (5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
Apache 2.0), with a map-preserving native Scheme.Modules readout. -/
module
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import NcCubic.Geometry.ModulesBridge
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
namespace NcCubic.Geometry.ProjectiveCohomology
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry

/-- The actual Serre twist is an equivalence, since every polynomial projective
space has a degree-one standard cover and the twisting sheaf is invertible. -/
theorem rawTwist_isEquivalence (A : Type u) [CommRing A] (n : ℕ) (k : ℤ) :
    (ProjTwistFunctor.twistFunctor (polyGrading A n) k).IsEquivalence := by
  have : Stacks.SheafOfModules.IsInvertible
      (ProjectiveSpectrum.Proj.structureSheaf (polyGrading A n)).obj
      (ProjTwistFunctor.projRingSheaf (polyGrading A n)).property
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) k) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      (ProjTwistDegreeOneCover.isInvertible_twistingSheaf (polyGrading A n)
        (ProjTwistRank.degreeOneCover_polyGrading A n) k)
  exact ProjTwistFunctor.isEquivalence_twistFunctor (polyGrading A n) k

/-- The same genuine tensor twist at the native scheme-module category spelling. -/
def projectiveTwist (A : Type u) [CommRing A] (n : ℕ) (k : ℤ) :
    (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules ⥤
      (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules where
  obj M := (ProjTwistFunctor.twistFunctor (polyGrading A n) k).obj M
  map f := (ProjTwistFunctor.twistFunctor (polyGrading A n) k).map f
  map_id M := (ProjTwistFunctor.twistFunctor (polyGrading A n) k).map_id M
  map_comp f g := (ProjTwistFunctor.twistFunctor (polyGrading A n) k).map_comp f g

instance (A : Type u) [CommRing A] (n : ℕ) (k : ℤ) :
    (projectiveTwist A n k).PreservesZeroMorphisms where
  map_zero M N := (ProjTwistFunctor.twistFunctor (polyGrading A n) k).map_zero M N

instance (A : Type u) [CommRing A] (n : ℕ) (k : ℤ) :
    (projectiveTwist A n k).Additive where
  map_add {X Y f g} := (ProjTwistFunctor.twistFunctor (polyGrading A n) k).map_add (f := f) (g := g)

instance (A : Type u) [CommRing A] (n : ℕ) (k : ℤ) :
    (projectiveTwist A n k).IsEquivalence := by
  exact rawTwist_isEquivalence A n k

/-- Short exactness is preserved by the actual twist of schemes' modules,
including the original morphisms acted on by the twist functor. -/
theorem shortExact_map_projectiveTwist (A : Type u) [CommRing A] (n : ℕ) (k : ℤ)
    {S : ShortComplex (_root_.AlgebraicGeometry.Proj (polyGrading A n)).Modules}
    (hS : S.ShortExact) : (S.map (projectiveTwist A n k)).ShortExact := by
  let := hS.mono_f
  let := hS.epi_g
  exact hS.map (projectiveTwist A n k)

/-- Twisting a finite sum of twisting sheaves acts componentwise by the
canonical multiplication of Serre twists. -/
def projectiveTwistSumIso (A : Type u) [CommRing A] (n : ℕ) (d k : ℤ) (r : ℕ) :
    (projectiveTwist A n k).obj (twistSum A n d r) ≅ twistSum A n (d + k) r := by
  let P : Scheme.{u} := _root_.AlgebraicGeometry.Proj (polyGrading A n)
  letI : HasFiniteBiproducts P.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  let G : Fin r → P.Modules := twistFamily A n d r
  let H : Fin r → P.Modules := twistFamily A n (d + k) r
  let F := projectiveTwist A n k
  letI : F.Additive := by dsimp only [F]; infer_instance
  letI : F.PreservesZeroMorphisms := by dsimp only [F]; infer_instance
  letI : PreservesBiproductsOfShape (Fin r) F := inferInstance
  letI : PreservesBiproductsOfShape (Fin r) (schemeModulesOfSite P) :=
    preservesBiproductsOfShape_of_preservesProductsOfShape _
  letI : HasFiniteBiproducts (_root_.SheafOfModules.{u} P.ringCatSheaf) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts (_root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥P) P.sheaf)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let e : ∀ i, F.obj (G i) ≅ H i := fun _ => tensorTwistingSheafIso A n d k
  let G0 : Fin r → _root_.SheafOfModules.{u} P.ringCatSheaf := twistFamily A n d r
  let H0 : Fin r → _root_.SheafOfModules.{u} P.ringCatSheaf := twistFamily A n (d+k) r
  letI : HasBiproduct G0 := HasBiproduct.of_hasProduct G0
  letI : HasBiproduct H0 := HasBiproduct.of_hasProduct H0
  let eSource : twistSum A n d r ≅ ⨁ G :=
    (schemeModulesOfSite P).mapBiproduct (C := _root_.SheafOfModules.{u} P.ringCatSheaf) G0
  let eTarget : twistSum A n (d+k) r ≅ ⨁ H :=
    (schemeModulesOfSite P).mapBiproduct (C := _root_.SheafOfModules.{u} P.ringCatSheaf) H0
  exact F.mapIso eSource ≪≫ F.mapBiproduct G ≪≫
    biproduct.mapIso (C := P.Modules) (f := fun i => F.obj (G i)) (g := H) e ≪≫
    eTarget.symm

end NcCubic.Geometry.ProjectiveCohomology
