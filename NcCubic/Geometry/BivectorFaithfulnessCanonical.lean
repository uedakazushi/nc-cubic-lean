/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.BivectorFaithfulness
public import NcCubic.Geometry.SmoothBivectorDuality
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
/-- Actual bivectors with finite locally free relative cotangent sheaf are
faithfully detected by their operations on all actual opens. -/
theorem algebraicBivectorBracket_ext
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials f)]
    (pi rho : AlgebraicBivector f)
    (h : ∀ (U : X.Opens) (a b : Γ(X,U)),
      (algebraicBivectorBracket f pi).bracket U a b =
        (algebraicBivectorBracket f rho).bracket U a b) : pi = rho :=
  algebraicBivectorBracket_ext_of_duality f (bivectorDualityIso f) (bivectorDualityIso_unit f) pi rho h

theorem algebraicBivectorBracket_ext_smooth [Smooth f] (pi rho : AlgebraicBivector f)
    (h : ∀ (U : X.Opens) (a b : Γ(X,U)),
      (algebraicBivectorBracket f pi).bracket U a b =
        (algebraicBivectorBracket f rho).bracket U a b) : pi = rho :=
  algebraicBivectorBracket_ext_of_duality f (smoothBivectorDualityIso f)
    (smoothBivectorDualityIso_unit f) pi rho h

theorem algebraicBivectorBracket_injective_smooth [Smooth f] :
    Function.Injective (algebraicBivectorBracket f) :=
  algebraicBivectorBracket_injective_of_duality f (smoothBivectorDualityIso f)
    (smoothBivectorDualityIso_unit f)

theorem algebraicBivector_eq_zero_of_bracket_zero [Smooth f] (pi : AlgebraicBivector f)
    (h : ∀ (U : X.Opens) (a b : Γ(X,U)), (algebraicBivectorBracket f pi).bracket U a b = 0) :
    pi = 0 :=
  algebraicBivector_eq_zero_of_bracket_zero_of_duality f (smoothBivectorDualityIso f)
    (smoothBivectorDualityIso_unit f) pi h
end NcCubic.Geometry
