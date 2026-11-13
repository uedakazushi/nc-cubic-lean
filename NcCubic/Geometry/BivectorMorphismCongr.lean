module
public import NcCubic.Geometry.BivectorSheafDesc
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Equality of structure morphisms transports actual global tangent bivectors
linearly over the unchanged ring of global functions. No comparison of concrete
Kähler or exterior-sheaf carriers is unfolded. -/
def bivectorCongr {X S : Scheme.{u}} {f g : X ⟶ S} (h : f = g) :
    AlgebraicBivector f ≃ₗ[Γ(X,⊤)] AlgebraicBivector g := by
  cases h
  exact LinearEquiv.refl _ _

/-- Transport along the reflexive morphism equality is the identity. -/
theorem bivectorCongr_rfl {X S : Scheme.{u}} (f : X ⟶ S)
    (pi : AlgebraicBivector f) : bivectorCongr (rfl : f=f) pi = pi := rfl

/-- Every actual open-ring operation is preserved by transport of the structure
morphism. This lemma is proved generically before any projective specialization. -/
theorem algebraicBivectorBracket_bivectorCongr {X S : Scheme.{u}} {f g : X ⟶ S}
    (h : f = g) (pi : AlgebraicBivector f) (U : X.Opens) (a b : Γ(X,U)) :
    (algebraicBivectorBracket g (bivectorCongr h pi)).bracket U a b =
      (algebraicBivectorBracket f pi).bracket U a b := by
  cases h
  rfl

/-- The same equality at the level of genuine structure-sheaf bracket data. -/
theorem algebraicBivectorBracket_bivectorCongr_eq {X S : Scheme.{u}} {f g : X ⟶ S}
    (h : f = g) (pi : AlgebraicBivector f) :
    algebraicBivectorBracket g (bivectorCongr h pi) = algebraicBivectorBracket f pi := by
  cases h
  rfl
end NcCubic.Geometry
