/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorFunctionalAgreement
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem exteriorFunctionalContraction_injective {X S : Scheme.{u}} (f : X ⟶ S) :
    Function.Injective (exteriorFunctionalContraction f) := by
  intro lam mu h
  apply ImmersionBracketNaturality.exteriorDual_ext_on_wedges
    (Scheme.Hom.relativeDifferentials f) ⊤ lam mu
  intro Z v
  let U := Z.left
  have hp : exteriorFunctionalPairing f lam U (v 0) (v 1) =
      exteriorFunctionalPairing f mu U (v 0) (v 1) :=
    (exteriorFunctionalContraction_eval f lam U (v 0) (v 1)).symm.trans
      ((congrArg (fun c => tangentEvaluation f U
        (contractionEvaluation f U ((tangentContractionSheaf f).presheaf.map
          (homOfLE le_top).op c) (v 0)) (v 1)) h).trans
        (exteriorFunctionalContraction_eval f mu U (v 0) (v 1)))
  have hv : ![v 0,v 1] = v := by
    funext i
    fin_cases i <;> rfl
  change dualPairing (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))
      lam (Over.mk (homOfLE (show U≤⊤ from le_top)))
      (exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials f) U ![v 0,v 1]) =
    dualPairing (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))
      mu (Over.mk (homOfLE (show U≤⊤ from le_top)))
      (exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials f) U ![v 0,v 1]) at hp
  rw [hv] at hp
  exact hp
end NcCubic.Geometry
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem algebraicBivectorBracket_ext_of_duality {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (e : bivectorSheaf f ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)))
    (he : HasUnitDeterminantFormula f e.hom) (pi rho : AlgebraicBivector f)
    (h : ∀ (U : X.Opens) (a b : Γ(X,U)),
      (algebraicBivectorBracket f pi).bracket U a b =
        (algebraicBivectorBracket f rho).bracket U a b) : pi = rho := by
  apply (CotangentCoordinates.moduleSectionsLinearEquiv e ⊤).injective
  change e.hom.app ⊤ pi = e.hom.app ⊤ rho
  apply exteriorFunctionalContraction_injective f
  apply contractionGlobalBracket_ext f
  intro U a b
  exact (exteriorFunctionalContraction_agrees_bracket f e.hom he pi U a b).trans
    ((h U a b).trans
      (exteriorFunctionalContraction_agrees_bracket f e.hom he rho U a b).symm)

set_option backward.isDefEq.respectTransparency false in
theorem algebraicBivectorBracket_injective_of_duality {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (e : bivectorSheaf f ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)))
    (he : HasUnitDeterminantFormula f e.hom) :
    Function.Injective (algebraicBivectorBracket f) := by
  intro pi rho h
  exact algebraicBivectorBracket_ext_of_duality f e he pi rho
    (fun U a b => congrArg (fun B : StructureSheafBracket X => B.bracket U a b) h)
end NcCubic.Geometry
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
theorem algebraicBivector_eq_zero_of_bracket_zero_of_duality {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (e : bivectorSheaf f ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)))
    (he : HasUnitDeterminantFormula f e.hom) (pi : AlgebraicBivector f)
    (h : ∀ (U : X.Opens) (a b : Γ(X,U)), (algebraicBivectorBracket f pi).bracket U a b = 0) :
    pi = 0 := by
  apply algebraicBivectorBracket_ext_of_duality f e he pi 0
  intro U a b
  exact (h U a b).trans (algebraicBivectorBracket_zero f U a b).symm
end NcCubic.Geometry
