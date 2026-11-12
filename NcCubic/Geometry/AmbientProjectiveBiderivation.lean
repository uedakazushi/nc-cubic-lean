/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.AmbientProjectiveRelative
public import NcCubic.Geometry.SheafBiderivation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace NcCubic.Geometry
universe u
variable {X : Scheme.{u}} {ι : Type u}
/-- Alternating biderivations on an actual basis, without Jacobi. -/
structure BasisBiderivationData (X : Scheme.{u}) (W : ι → X.Opens)
    extends BasisBracketData X W where
  add_right (i) (a b c : Γ(X,W i)) : bracket i a (b+c) = bracket i a b + bracket i a c
  skew (i) (a b : Γ(X,W i)) : bracket i a b = -bracket i b a
  self_eq_zero (i) (a : Γ(X,W i)) : bracket i a a = 0
  leibniz (i) (a b c : Γ(X,W i)) : bracket i a (b*c) = b*bracket i a c + c*bracket i a b

def BasisBiderivationData.glued {W : ι → X.Opens} (D : BasisBiderivationData X W) :
    StructureSheafBiderivation X where
  toStructureSheafBracket := D.toBasisBracketData.glued
  add_right U a b c := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op)
      (D.toBasisBracketData.gluedBracket U a (b+c)) =
      (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a b + D.toBasisBracketData.gluedBracket U a c)
    simp only [map_add, BasisBracketData.gluedBracket_restrict]
    exact D.add_right i _ _ _
  skew U a b := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a b) =
      (X.presheaf.map (homOfLE hi).op) (-D.toBasisBracketData.gluedBracket U b a)
    simp only [map_neg, BasisBracketData.gluedBracket_restrict]
    exact D.skew i _ _
  self_eq_zero U a := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a a) =
      (X.presheaf.map (homOfLE hi).op) 0
    simp only [map_zero, BasisBracketData.gluedBracket_restrict]
    exact D.self_eq_zero i _
  leibniz U a b c := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a (b*c)) =
      (X.presheaf.map (homOfLE hi).op) (b*D.toBasisBracketData.gluedBracket U a c + c*D.toBasisBracketData.gluedBracket U a b)
    simp only [map_add, map_mul, BasisBracketData.gluedBracket_restrict]
    exact D.leibniz i _ _ _

theorem BasisBiderivationData.glued_restrict {W : ι → X.Opens} (D : BasisBiderivationData X W)
    (U : X.Opens) (a b : Γ(X,U)) (i : ι) (hi : W i ≤ U) :
    (X.presheaf.map (homOfLE hi).op) (D.glued.bracket U a b) =
      D.bracket i ((X.presheaf.map (homOfLE hi).op) a) ((X.presheaf.map (homOfLE hi).op) b) :=
  D.toBasisBracketData.gluedBracket_restrict U a b i hi

theorem BasisBiderivationData.glued_relative {R : Type u} [CommRing R]
    {W : ι → X.Opens} (D : BasisBiderivationData X W)
    (f : X ⟶ Spec (CommRingCat.of R))
    (hR : ∀ i a r, D.bracket i a (AffineSmoothness.coefficientMap f (W i) r) = 0) :
    D.glued.IsRelative f := by
  intro U a r
  apply D.toBasisBracketData.eq_of_basis
  intro i hi
  rw [D.glued_restrict, map_zero]
  have hc : (X.presheaf.map (homOfLE hi).op) (AffineSmoothness.coefficientMap f U r) =
      AffineSmoothness.coefficientMap f (W i) r := by
    unfold AffineSmoothness.coefficientMap
    simp only [RingHom.comp_apply]
    have h := f.appLE_map (U := ⊤) (V := U) (V' := W i) le_top (homOfLE hi).op
    exact congrArg (fun g => g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  rw [hc]
  exact hR i _ r

variable {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
/-- The genuine homogeneous basis carries a biderivation without any Jacobi input. -/
def ambientBasisBiderivation
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j) :
    BasisBiderivationData (ProjectiveAmbient n) positiveBasicOpen where
  toBasisBracketData := ambientBasisBracket q hq
  add_right s := HomogeneousSections.bracket_add_right q hq s.1.pos s.2.property
  skew s := HomogeneousSections.bracket_skew q hq hskew s.1.pos s.2.property
  self_eq_zero s := HomogeneousSections.bracket_self q hq hskew s.1.pos s.2.property
  leibniz s := HomogeneousSections.bracket_leibniz q hq s.1.pos s.2.property

/-- Every skew homogeneous quadratic array gives an actual all-open alternating
biderivation. Jacobi is deliberately not an input to this construction. -/
def ambientProjectiveBiderivation
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j) :
    StructureSheafBiderivation (ProjectiveAmbient n) :=
  (ambientBasisBiderivation q hq hskew).glued

@[simp] theorem ambientProjectiveBiderivation_toBracket
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j) :
    (ambientProjectiveBiderivation q hq hskew).toStructureSheafBracket =
      ambientProjectiveBracket q hq := rfl

/-- Relative scalar compatibility is proved on the genuine homogeneous basis
and transported through actual structure-sheaf restriction maps. -/
theorem ambientProjectiveBiderivation_relative
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j) :
    (ambientProjectiveBiderivation q hq hskew).IsRelative
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) := by
  apply (ambientBasisBiderivation q hq hskew).glued_relative
  intro i a c
  have hi : (i.2 : CubicPolynomial (n+1)).IsHomogeneous (i.1 : ℕ) := i.2.property
  change HomogeneousSections.bracket q hq i.1.pos hi a
    (AffineSmoothness.coefficientMap _
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ)
        (i.2 : CubicPolynomial (n+1))) c) = 0
  rw [homogeneous_coefficientMap_eq_constant i.1.pos hi]
  exact HomogeneousSections.bracket_constant_right q hq i.1.pos hi a c
end NcCubic.Geometry
