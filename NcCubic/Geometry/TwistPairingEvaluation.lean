/- Exact local evaluation of the actual graded twist multiplication pairing. -/
module
public import NcCubic.Geometry.CanonicalTwistDuality
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
attribute [local implicit_reducible] Tensor.ringSheaf TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Type u} {σ : Type u} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (g : ℕ → σ) [GradedRing g]
lemma gradedCast_val {a b : ℤ} (h : a = b) (U : (AlgebraicGeometry.Proj g).Opens)
    (s : (twistingSheaf g a).val.obj (op U)) (x : U) :
    (((eqToHom (congrArg (twistingSheaf g) h)).val.app (op U) s).1 x) = s.1 x := by
  cases h
  rfl
lemma gradedPairing_tmul_val (d : ℤ) (U : (AlgebraicGeometry.Proj g).Opens)
    (s : (twistingSheaf g d).val.obj (op U))
    (t : (twistingSheaf g (-d)).val.obj (op U)) (x : U) :
    HomogeneousLocalization.val
      ((((twistMultiplicationMap g d (-d) ≫
        eqToHom (congrArg (twistingSheaf g) (add_neg_cancel d))) ≫
        (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit g).hom).val.app (op U)
        (toTensorSheafSection (AlgebraicGeometry.Proj g).toRingedSpace
          (twistingSheaf g d) (twistingSheaf g (-d)) (op U) (s ⊗ₜ[_] t))).1 x) = s.1 x * t.1 x := by
  let z := toTensorSheafSection (AlgebraicGeometry.Proj g).toRingedSpace
    (twistingSheaf g d) (twistingSheaf g (-d)) (op U) (s ⊗ₜ[_] t)
  exact (Stacks.AlgebraicGeometry.ProjEulerSequence.val_comp_twistingSheafZeroIsoUnit_hom_apply
    g (twistMultiplicationMap g d (-d) ≫ eqToHom (congrArg (twistingSheaf g) (add_neg_cancel d))) U z x).trans
    ((gradedCast_val g (add_neg_cancel d) U
      ((twistMultiplicationMap g d (-d)).val.app (op U) z) x).trans
      (Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul g d (-d) U s t x))
end NcCubic.Geometry.CanonicalTwistDuality
