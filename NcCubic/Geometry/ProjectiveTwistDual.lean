/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ModulesBridge
public import NcCubic.Geometry.ProjectiveTwistInverse
public import StacksFrontier.AlgebraicGeometry.Modules.DualBiproduct
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
open CategoryTheory AlgebraicGeometry
namespace NcCubic.Geometry.ProjectiveCohomology
universe u
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] hasFiniteBiproducts_toRingCat
open CategoryTheory.Limits

/-- The dual of a genuine finite biproduct is the biproduct of the actual sheaf
of duals. This comparison preserves the dual projection and inclusion maps. -/
def dualBiproductIso (X : Scheme.{u}) {ι : Type*} [Finite ι]
    (F : ι → X.Modules) [HasBiproduct F]
    [HasBiproduct (fun i => dualSheaf (X := X) (F i))] :
    dualSheaf (X := X) (⨁ F) ≅ ⨁ (fun i => dualSheaf (X := X) (F i)) :=
  biproduct.uniqueUpToIso _
    (dualBicone_isBilimit (X := X) (biproduct.bicone F) (biproduct.isBilimit F))

/-- Dual middle term compared through bare biproduct isomorphisms. -/
def dualEulerMiddleIso (A : Type u) [CommRing A] (n : ℕ) :
    dualSheaf (X := _root_.AlgebraicGeometry.Proj (polyGrading A n))
      (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum A n) ≅
        twistSum A n 1 (n + 1) := by
  let X : Scheme.{u} := _root_.AlgebraicGeometry.Proj (polyGrading A n)
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts (_root_.SheafOfModules.{u} X.ringCatSheaf) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteBiproducts (_root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology ↥X) X.sheaf)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : PreservesBiproductsOfShape (Fin (n + 1)) (schemeModulesOfSite X) :=
    preservesBiproductsOfShape_of_preservesProductsOfShape _
  let F0 : Fin (n + 1) → _root_.SheafOfModules.{u} X.ringCatSheaf :=
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n
  let G0 : Fin (n + 1) → _root_.SheafOfModules.{u} X.ringCatSheaf :=
    twistFamily A n 1 (n + 1)
  letI : HasBiproduct F0 := HasBiproduct.of_hasProduct F0
  letI : HasBiproduct G0 := HasBiproduct.of_hasProduct G0
  let F : Fin (n + 1) → X.Modules :=
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n
  let G : Fin (n + 1) → X.Modules := twistFamily A n 1 (n + 1)
  let eNeg : Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneSum A n ≅ ⨁ F :=
    (schemeModulesOfSite X).mapBiproduct (C := _root_.SheafOfModules.{u} X.ringCatSheaf)
      F0
  let ePos : twistSum A n 1 (n + 1) ≅ ⨁ G :=
    (schemeModulesOfSite X).mapBiproduct (C := _root_.SheafOfModules.{u} X.ringCatSheaf) G0
  let e : ∀ i, dualSheaf (F i) ≅ G i := fun _ =>
    (twistNegIsoDual A n (-1)).symm
  exact (dualSheafIsoOfIso (X := X) eNeg).symm ≪≫ dualBiproductIso X F ≪≫
    biproduct.mapIso (C := X.Modules) (f := fun i => dualSheaf (F i)) (g := G) e ≪≫
    ePos.symm
end NcCubic.Geometry.ProjectiveCohomology
