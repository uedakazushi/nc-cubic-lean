/- Canonical projective twist duality from the actual multiplication pairing. -/
module
public import NcCubic.Geometry.TensorCurryIso
public import NcCubic.Geometry.ModulesBridge
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite TopologicalSpace TensorProduct
universe u
namespace NcCubic.Geometry.CanonicalTwistDuality
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open AlgebraicGeometry.ProjectiveSpectrum.Proj
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Tensor.ringSheaf

abbrev projective (A : Type u) [CommRing A] (n : ℕ) := AlgebraicGeometry.Proj (polyGrading A n)
abbrev twist (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    _root_.SheafOfModules.{u} (structureSheafRing (projective A n).toRingedSpace) :=
  twistingSheaf (polyGrading A n) d

/-- The literal multiplication map, followed only by the degree-zero comparison. -/
def twistPairing (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    ((Tensor.sheafTensor (projective A n).sheaf).obj (twist A n d)).obj (twist A n (-d)) ⟶
      SheafOfModules.unit (structureSheafRing (projective A n).toRingedSpace) :=
  twistMultiplicationMap (polyGrading A n) d (-d) ≫
    eqToHom (congrArg (twist A n) (add_neg_cancel d)) ≫
    (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading A n)).hom

/-- This isomorphism is built only from actual twist multiplication and its degree-zero target. -/
def twistPairingIso (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    ((Tensor.sheafTensor (projective A n).sheaf).obj (twist A n d)).obj (twist A n (-d)) ≅
      SheafOfModules.unit (structureSheafRing (projective A n).toRingedSpace) :=
  tensorTwistingSheafIso A n d (-d) ≪≫
    eqToIso (congrArg (twist A n) (add_neg_cancel d)) ≪≫
    Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading A n)

@[simp] lemma twistPairingIso_hom (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    (twistPairingIso A n d).hom = twistPairing A n d := rfl

lemma twistPairing_isIso (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    @IsIso (_root_.SheafOfModules.{u} (Tensor.ringSheaf (projective A n).sheaf))
      inferInstance _ _ (twistPairing A n d) :=
  (twistPairingIso A n d).isIso_hom

/-- Currying the actual multiplication, not choosing an abstract inverse object iso. -/
def twistCurryMap (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    twist A n d ⟶ SheafTensorCurry.sheafHomSpace (projective A n).toRingedSpace
      (twist A n (-d)) (SheafOfModules.unit (structureSheafRing (projective A n).toRingedSpace)) :=
  SheafTensorCurry.tensorHomEquiv (projective A n).toRingedSpace
    (twist A n d) (twist A n (-d))
    (SheafOfModules.unit (structureSheafRing (projective A n).toRingedSpace)) (twistPairing A n d)

lemma twistCurryMap_isTensorCurry (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    SheafTensorCurry.IsTensorCurry (projective A n).toRingedSpace
      (twistPairing A n d) (twistCurryMap A n d) :=
  SheafTensorCurry.tensorHomEquiv_isTensorCurry (projective A n).toRingedSpace (twistPairing A n d)

lemma twistCurryMap_isIso (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    @IsIso (_root_.SheafOfModules.{u} (structureSheafRing (projective A n).toRingedSpace))
      inferInstance _ _ (twistCurryMap A n d) :=
  isIso_curry_of_pairingIso (projective A n).toRingedSpace
    (twist A n d) (twist A n (-d)) (twistPairingIso A n d)

def twistCurryIso (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    twist A n d ≅ SheafTensorCurry.sheafHomSpace (projective A n).toRingedSpace
      (twist A n (-d)) (SheafOfModules.unit (structureSheafRing (projective A n).toRingedSpace)) :=
  @asIso _ _ _ _ (twistCurryMap A n d) (twistCurryMap_isIso A n d)

/-- The same canonical multiplication curry at the native scheme-module spelling. -/
def twistDualMap (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    (twist A n d : (projective A n).Modules) ⟶
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (X := projective A n) (twist A n (-d)) :=
  (schemeModulesOfSite (projective A n)).map (twistCurryMap A n d)

def twistDualIso (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    (twist A n d : (projective A n).Modules) ≅
      Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (X := projective A n) (twist A n (-d)) :=
  (schemeModulesOfSite (projective A n)).mapIso (twistCurryIso A n d)

lemma twistDualMap_isIso (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    @IsIso (projective A n).Modules inferInstance _ _ (twistDualMap A n d) :=
  (twistDualIso A n d).isIso_hom

lemma twistDualMap_isTensorCurry (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    SheafTensorCurry.IsTensorCurry (projective A n).toRingedSpace
      (twistPairing A n d) (twistDualMap A n d) :=
  twistCurryMap_isTensorCurry A n d


lemma castTwistSection_val (A : Type u) [CommRing A] (n : ℕ)
    {a b : ℤ} (h : a = b) (U : (projective A n).Opens)
    (s : (twist A n a).val.obj (op U)) (x : U) :
    (((eqToHom (congrArg (twist A n) h)).val.app (op U) s).1 x) = s.1 x := by
  cases h
  rfl


end NcCubic.Geometry.CanonicalTwistDuality
