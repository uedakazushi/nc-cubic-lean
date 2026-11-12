/- Local evaluation of canonical twist duality is actual multiplication. -/
module
public import NcCubic.Geometry.TwistPairingEvaluation
public import NcCubic.Geometry.ModulesBridge
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSum
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic
set_option Elab.async false
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

/-- The pairing evaluates to multiplication of the actual localized values. -/
lemma twistPairing_tmul_val (A : Type u) [CommRing A] (n : ℕ) (d : ℤ)
    (U : (projective A n).Opens)
    (s : (twist A n d).val.obj (op U)) (t : (twist A n (-d)).val.obj (op U)) (x : U) :
    HomogeneousLocalization.val
      (((twistPairing A n d).val.app (op U)
        (toTensorSheafSection (projective A n).toRingedSpace
          (twist A n d) (twist A n (-d)) (op U) (s ⊗ₜ[_] t))).1 x) = s.1 x * t.1 x := by
  exact gradedPairing_tmul_val (polyGrading A n) d U s t x

/-- Pointwise evaluation of the canonical positive/negative twist duality:
no unidentified object isomorphism occurs in this formula. -/
lemma twistDualMap_eval_val (A : Type u) [CommRing A] (n : ℕ) (d : ℤ)
    (U : (projective A n).Opens)
    (s : (twist A n d).val.obj (op U)) (t : (twist A n (-d)).val.obj (op U)) (x : U) :
    HomogeneousLocalization.val
      ((((((twistDualMap A n d).val.app (op U) s).app
        (op (Over.mk (𝟙 U)))).hom t)).1 x) = s.1 x * t.1 x := by
  have h := twistDualMap_isTensorCurry A n d U s t
  exact (congrArg
    (fun r : (SheafOfModules.unit (structureSheafRing (projective A n).toRingedSpace)).val.obj (op U) =>
      HomogeneousLocalization.val (r.1 x)) h).trans (twistPairing_tmul_val A n d U s t x)

@[simp] lemma twistDualIso_hom (A : Type u) [CommRing A] (n : ℕ) (d : ℤ) :
    (twistDualIso A n d).hom = twistDualMap A n d := rfl

/-- Native sheaf-dual pairing is exactly the original multiplication on local pure tensors. -/
lemma twistDualMap_pairing (A : Type u) [CommRing A] (n : ℕ) (d : ℤ)
    (U : (projective A n).Opens)
    (s : Γ((twist A n d : (projective A n).Modules), U))
    (t : Γ((twist A n (-d) : (projective A n).Modules), U)) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualPairing (twist A n (-d))
      ((twistDualMap A n d).val.app (op U) s) (Over.mk (𝟙 U)) t =
      (twistPairing A n d).val.app (op U)
        (toTensorSheafSection (projective A n).toRingedSpace
          (twist A n d) (twist A n (-d)) (op U) (s ⊗ₜ[_] t)) :=
  twistDualMap_isTensorCurry A n d U s t

lemma twistDualMap_pairing_val (A : Type u) [CommRing A] (n : ℕ) (d : ℤ)
    (U : (projective A n).Opens)
    (s : Γ((twist A n d : (projective A n).Modules), U))
    (t : Γ((twist A n (-d) : (projective A n).Modules), U)) (x : U) :
    HomogeneousLocalization.val
      ((Stacks.AlgebraicGeometry.ReflexiveModules.dualPairing (twist A n (-d))
        ((twistDualMap A n d).val.app (op U) s) (Over.mk (𝟙 U)) t).1 x) = s.1 x * t.1 x :=
  twistDualMap_eval_val A n d U s t x

end NcCubic.Geometry.CanonicalTwistDuality
