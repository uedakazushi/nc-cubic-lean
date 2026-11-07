/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.TangentNaturality
public import NcCubic.Geometry.AffineSmoothness
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
/-- A genuine relative tangent-sheaf section induces an R-derivation on each
actual open section ring with its actual structure-map algebra. -/
def tangentSectionRelativeDerivation (U : X.Opens) (t : Γ(tangentSheaf f,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Derivation R Γ(X,U) Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  let D := tangentSectionDerivation f U t
  apply Derivation.mk' {
    toFun := D
    map_add' := D.map_add
    map_smul' := ?_ }
  · intro a b
    exact D.leibniz a b
  · intro r a
    change D (AffineSmoothness.coefficientMap f U r * a) =
      AffineSmoothness.coefficientMap f U r * D a
    rw [Derivation.leibniz]
    have hz : D (AffineSmoothness.coefficientMap f U r) = 0 :=
      tangentSectionDerivation_base_appLE f ⊤ U le_top t
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
    rw [hz, smul_zero, add_zero]
    rfl
@[simp] theorem tangentSectionRelativeDerivation_apply (U : X.Opens)
    (t : Γ(tangentSheaf f,U)) (a : Γ(X,U)) :
    tangentSectionRelativeDerivation f U t a = tangentSectionDerivation f U t a := rfl

/-- The tangent action is linear over the actual ring of local functions. -/
def tangentSectionRelativeDerivationLinear (U : X.Opens) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Γ(tangentSheaf f,U) →ₗ[Γ(X,U)] Derivation R Γ(X,U) Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact {
    toFun := tangentSectionRelativeDerivation f U
    map_add' := fun t s => by ext a; exact tangentEvaluation_add f U t s _
    map_smul' := fun r t => by ext a; exact tangentEvaluation_smul f U r t _ }

/-- Canonical evaluation of genuine tangent sections on the algebraic Kähler
module of the section ring. This is a map, with no arbitrary-open isomorphism claim. -/
def tangentSectionKahlerDual (U : X.Opens) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Γ(tangentSheaf f,U) →ₗ[Γ(X,U)]
      Module.Dual Γ(X,U) (KaehlerDifferential R Γ(X,U)) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact (KaehlerDifferential.linearMapEquivDerivation (M := Γ(X,U)) R Γ(X,U)).symm.toLinearMap.comp
    (tangentSectionRelativeDerivationLinear f U)

@[simp] theorem tangentSectionKahlerDual_d (U : X.Opens) (t : Γ(tangentSheaf f,U))
    (a : Γ(X,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    tangentSectionKahlerDual f U t (KaehlerDifferential.D R Γ(X,U) a) =
      tangentEvaluation f U t ((Scheme.Hom.universalRelativeDerivation f).d a) := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  change (tangentSectionRelativeDerivation f U t).liftKaehlerDifferential
    (KaehlerDifferential.D R Γ(X,U) a) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  rfl
end NcCubic.Geometry
