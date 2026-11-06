/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Canonical relative cotangent morphism and its actual derivation compatibility.
-/
module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Functoriality
@[expose] public section
universe u
namespace NcCubic.Geometry.ImmersionBivector
noncomputable section
open AlgebraicGeometry CategoryTheory

variable {X P S : Scheme.{u}}

/-- The canonical cotangent map for a morphism over the fixed base. It exists
without any normal-sequence or smoothness assumption. -/
def cotangentMap (i : X ⟶ P) (p : P ⟶ S) :
    (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) ⟶
      Scheme.Hom.relativeDifferentials (i ≫ p) :=
  Scheme.Hom.relativeDifferentialsMap i p (i ≫ p) (𝟙 S) (by simp)

theorem cotangentMap_compatible (i : X ⟶ P) (p : P ⟶ S) :
    Scheme.Hom.IsRelativeDifferentialsMap i p (i ≫ p) (cotangentMap i p) :=
  (Scheme.Hom.isRelativeDifferentialsMap_iff_eq i p (i ≫ p) (𝟙 S) (by simp) _).mpr rfl

/-- On every local function the actual cotangent map sends its differential
to the differential of its pullback. -/
theorem cotangentMap_on_differentials (i : X ⟶ P) (p : P ⟶ S)
    (U : P.Opens) (f : Γ(P, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv
      (Scheme.Hom.relativeDifferentials p) (Scheme.Hom.relativeDifferentials (i ≫ p))
        (cotangentMap i p)).val.app (.op U)).hom
          ((Scheme.Hom.universalRelativeDerivation p).d f) =
      (Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U).hom f) :=
  cotangentMap_compatible i p U f


end
end NcCubic.Geometry.ImmersionBivector
