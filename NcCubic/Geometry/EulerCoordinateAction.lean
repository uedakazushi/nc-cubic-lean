/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.EulerTangentAction
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u v w a
section Generic
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {ι : Type*} [Fintype ι]
    (F : ι → SheafOfModules.{a} R) [HasBiproduct F]
theorem sheaf_biproduct_projection_sum (V : Cᵒᵖ)
    (t : ∀ i, (F i).val.obj V) (j : ι) :
    (biproduct.π F j).val.app V (∑ i, (biproduct.ι F i).val.app V (t i)) = t j := by
  change ((biproduct.π F j).val.app V).hom (∑ i, (biproduct.ι F i).val.app V (t i)) = t j
  rw [map_sum]
  rw [Finset.sum_eq_single j]
  · have h := congrArg (fun k : F j ⟶ F j => k.val.app V (t j)) (biproduct.ι_π_self F j)
    exact h
  · intro i _ hij
    have h := congrArg (fun k : F i ⟶ F j => k.val.app V (t i)) (biproduct.ι_π_ne F hij)
    exact h
  · intro hj
    exact (hj (Finset.mem_univ j)).elim
end Generic
attribute [local instance] MvPolynomial.gradedAlgebra
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ReflexiveModules
variable (R : Type u) [CommRing R] (n : ℕ)

theorem eulerFirstArrow_component_on_d
    (U : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (j : Fin (n+1)) (a : Γ(AlgebraicGeometry.Proj (polyGrading R n),U)) :
    (biproduct.π (twistMinusOneFamily R n) j).val.app (op U)
      ((eulerFirstArrow R n).val.app (op U)
        ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d a)) =
      pderivApp R n j U a := by
  exact (congrArg (fun z => (biproduct.π (twistMinusOneFamily R n) j).val.app (op U) z)
    (eulerFirstArrow_on_d R n U a)).trans
    (sheaf_biproduct_projection_sum (twistMinusOneFamily R n) (op U)
      (fun i => pderivApp R n i U a) j)

/-- The actual tangent Euler quotient on one dual coordinate summand. -/
def eulerTangentColumn (j : Fin (n+1)) :
    dualSheaf (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistMinusOneFamily R n j) ⟶
      tangentSheaf (X := AlgebraicGeometry.Proj (polyGrading R n))
      (S := Spec (CommRingCat.of R)) (projToSpecCoeff R n) :=
  dualMap (X := AlgebraicGeometry.Proj (polyGrading R n))
    (biproduct.π (twistMinusOneFamily R n) j) ≫ eulerTangentMap R n

/-- Coordinate Euler fields act by pairing with the corresponding twisted derivative. -/
theorem eulerTangentColumn_action
    (U : (AlgebraicGeometry.Proj (polyGrading R n)).Opens) (j : Fin (n+1))
    (t : Γ(dualSheaf (X := AlgebraicGeometry.Proj (polyGrading R n))
      (twistMinusOneFamily R n j),U))
    (a : Γ(AlgebraicGeometry.Proj (polyGrading R n),U)) :
    tangentSectionDerivation (projToSpecCoeff R n) U
      (Scheme.Modules.Hom.app (eulerTangentColumn R n j) U t) a =
      dualPairing (X := AlgebraicGeometry.Proj (polyGrading R n))
        (twistMinusOneFamily R n j) t (Over.mk (𝟙 U)) (pderivApp R n j U a) := by
  let t' := Scheme.Modules.Hom.app (dualMap (X := AlgebraicGeometry.Proj (polyGrading R n))
    (biproduct.π (twistMinusOneFamily R n) j)) U t
  change dualPairing (X := AlgebraicGeometry.Proj (polyGrading R n)) (projDifferentials R n)
    (Scheme.Modules.Hom.app (dualMap (X := AlgebraicGeometry.Proj (polyGrading R n))
      (eulerFirstArrow R n)) U t') (Over.mk (𝟙 U))
      ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d a) = _
  exact (dualPairing_dualMap (X := AlgebraicGeometry.Proj (polyGrading R n))
    (eulerFirstArrow R n) t' (Over.mk (𝟙 U))
    ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d a)).trans
    ((dualPairing_dualMap (X := AlgebraicGeometry.Proj (polyGrading R n))
      (biproduct.π (twistMinusOneFamily R n) j) t (Over.mk (𝟙 U))
      ((eulerFirstArrow R n).val.app (op U)
        ((Scheme.Hom.universalRelativeDerivation (projToSpecCoeff R n)).d a))).trans
      (congrArg (dualPairing (X := AlgebraicGeometry.Proj (polyGrading R n))
        (twistMinusOneFamily R n j) t (Over.mk (𝟙 U))) (eulerFirstArrow_component_on_d R n U j a)))
end NcCubic.Geometry
