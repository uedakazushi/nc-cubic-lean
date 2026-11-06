/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.ProjectiveSectionBracket
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 600000
variable {n : ℕ}

/-- Arbitrary actual structure-sheaf sections satisfy the overlap condition,
with no source-ring representative supplied as a hypothesis. -/
theorem projectiveSectionBracket_overlap_of_restrictions
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i j : Fin (n+1))
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)))
    (c d : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X j)))
    (ha : sectionRestrictionLeft i j a = sectionRestrictionRight i j c)
    (hb : sectionRestrictionLeft i j b = sectionRestrictionRight i j d) :
    sectionRestrictionLeft i j (projectiveSectionBracket F P hF i a b) =
      sectionRestrictionRight i j (projectiveSectionBracket F P hF j c d) := by
  let ei := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
  let ej := homogeneousSectionsEquiv (isHomogeneous_X ℂ j) (by omega)
  let e := homogeneousSectionsEquiv ((isHomogeneous_X ℂ i).mul (isHomogeneous_X ℂ j)) (by omega)
  have hleft (a) : e (projectiveRestriction i (isHomogeneous_X ℂ j) rfl (ei.symm a)) =
      sectionRestrictionLeft i j a := by
    calc
      _ = sectionRestrictionLeft i j (ei (ei.symm a)) :=
        homogeneousSectionsEquiv_restrict i (isHomogeneous_X ℂ j) rfl (ei.symm a)
      _ = _ := by rw [RingEquiv.apply_symm_apply]
  have hright (a) : e (projectiveRestriction j (isHomogeneous_X ℂ i)
      (mul_comm (X i) (X j)) (ej.symm a)) = sectionRestrictionRight i j a := by
    calc
      _ = sectionRestrictionRight i j (ej (ej.symm a)) :=
        homogeneousSectionsEquiv_restrict j (isHomogeneous_X ℂ i)
          (mul_comm (X i) (X j)) (ej.symm a)
      _ = _ := by rw [RingEquiv.apply_symm_apply]
  have hai := e.injective ((hleft a).trans (ha.trans (hright c).symm))
  have hbi := e.injective ((hleft b).trans (hb.trans (hright d).symm))
  have hh := projectiveSectionBracket_overlap F P hF i j
    (ei.symm a) (ei.symm b) (ej.symm c) (ej.symm d) hai hbi
  simpa only [ei,ej,RingEquiv.apply_symm_apply] using hh
end NcCubic.Geometry
