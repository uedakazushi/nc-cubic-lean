/-
Copyright (c) 2026 nc-cubic-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import NcCubic.Geometry.TangentSheaf
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Basic
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
/-- The actual quotient map in the tangent Euler sequence, as a morphism into
the genuine relative tangent sheaf. -/
def eulerTangentMap : dualSheaf (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n) ⟶
    tangentSheaf (X := AlgebraicGeometry.Proj (polyGrading R n))
      (S := Spec (CommRingCat.of R)) (projToSpecCoeff R n) := dualMap (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)

/-- The actual cotangent Euler map on the universal differential of any local
function, with the canonical coordinate partial derivatives. -/
theorem eulerFirstArrow_on_d (U : (AlgebraicGeometry.Proj (polyGrading R n)).Opens) (a : Γ(AlgebraicGeometry.Proj (polyGrading R n),U)) :
    (eulerFirstArrow R n).val.app (op U)
      ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d a) =
      ∑ j : Fin (n+1), (biproduct.ι (twistMinusOneFamily R n) j).val.app (op U)
        (pderivApp R n j U a) := by
  have h := congrArg (fun D : AlgebraicGeometry.SheafOfModules.SheafDerivation
    (AlgebraicGeometry.inverseImageStructureMap (projToSpecCoeff R n))
    (twistMinusOneSum R n) => D.d a)
    (universalRelativeDerivation_postcomp_eulerFirstArrow R n)
  exact h.trans (eulerDerivation_d R n a)

/-- Evaluation of the tangent Euler quotient is canonically dual to the
coordinate derivative Euler map, on every genuine open section ring. -/
theorem eulerTangentMap_action (U : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (t : Γ(dualSheaf (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n),U)) (a : Γ(AlgebraicGeometry.Proj (polyGrading R n),U)) :
    tangentSectionDerivation (projToSpecCoeff R n) U
      (Scheme.Modules.Hom.app (eulerTangentMap R n) U t) a =
      dualPairing (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n) t (Over.mk (𝟙 U))
        (∑ j : Fin (n+1), (biproduct.ι (twistMinusOneFamily R n) j).val.app (op U)
          (pderivApp R n j U a)) := by
  change dualPairing (X := AlgebraicGeometry.Proj (polyGrading R n)) (projDifferentials R n)
    (Scheme.Modules.Hom.app (dualMap (X := AlgebraicGeometry.Proj (polyGrading R n)) (eulerFirstArrow R n)) U t) (Over.mk (𝟙 U))
    ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d a) = _
  exact (dualPairing_dualMap (X := AlgebraicGeometry.Proj (polyGrading R n))
    (eulerFirstArrow R n) t (Over.mk (𝟙 U))
    ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d a)).trans
    (congrArg (dualPairing (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneSum R n) t (Over.mk (𝟙 U))) (eulerFirstArrow_on_d R n U a))
/-- Componentwise form of the actual Euler quotient action. -/
theorem eulerTangentMap_action_sum (U : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (t : Γ(dualSheaf (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneSum R n),U))
    (a : Γ(AlgebraicGeometry.Proj (polyGrading R n),U)) :
    tangentSectionDerivation (projToSpecCoeff R n) U
      (Scheme.Modules.Hom.app (eulerTangentMap R n) U t) a =
      ∑ j : Fin (n+1), dualPairing (X := AlgebraicGeometry.Proj (polyGrading R n))
        (twistMinusOneSum R n) t (Over.mk (𝟙 U))
        ((biproduct.ι (twistMinusOneFamily R n) j).val.app (op U)
          (pderivApp R n j U a)) := by
  rw [eulerTangentMap_action]
  exact map_sum (t.app (op (Over.mk (𝟙 U)))).hom _ _
end NcCubic.Geometry
