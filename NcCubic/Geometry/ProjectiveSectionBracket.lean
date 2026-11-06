/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.ProjectiveOverlap
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

abbrev ProjectiveAmbient (n : ℕ) := Proj (homogeneousSubmodule (Fin (n+1)) ℂ)

/-- The canonical identification with actual structure-sheaf sections on a
homogeneous projective basic open. -/
def homogeneousSectionsEquiv {d : ℕ} {f : CubicPolynomial (n+1)}
    (hf : f.IsHomogeneous d) (hd : 0 < d) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n+1)) ℂ) f ≃+*
      Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) f) :=
  (Proj.basicOpenIsoAway (homogeneousSubmodule (Fin (n+1)) ℂ) f hf hd).commRingCatIsoToRingEquiv

@[simp] theorem homogeneousSectionsEquiv_apply {d : ℕ} {f : CubicPolynomial (n+1)}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (a : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n+1)) ℂ) f) :
    homogeneousSectionsEquiv hf hd a =
      (Proj.awayToSection (homogeneousSubmodule (Fin (n+1)) ℂ) f).hom a := by
  change ((Proj.basicOpenIsoAway (homogeneousSubmodule (Fin (n+1)) ℂ) f hf hd).hom).hom a = _
  rw [Proj.basicOpenIsoAway_hom]

/-- The actual restriction of projective structure-sheaf sections agrees
with the proven homogeneous-localization transition map. -/
theorem homogeneousSectionsEquiv_restrict
    (i : Fin (n+1)) {d : ℕ} {g x : CubicPolynomial (n+1)}
    (hg : g.IsHomogeneous d) (hx : x = X i*g) (a : ProjectiveChartRing i) :
    homogeneousSectionsEquiv (hx ▸ (isHomogeneous_X ℂ i).mul hg) (by omega)
      (projectiveRestriction i hg hx a) =
    (ProjectiveAmbient n).presheaf.map
      (homOfLE (Proj.basicOpen_mono _ _ _ ⟨g,hx⟩)).op
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega) a) := by
  simp only [homogeneousSectionsEquiv_apply]
  have hh := congrArg
    (fun f : CommRingCat.of (ProjectiveChartRing i) ⟶
      Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) x) => f.hom a)
    (Proj.awayMap_awayToSection (homogeneousSubmodule (Fin (n+1)) ℂ)
      (show g ∈ homogeneousSubmodule (Fin (n+1)) ℂ d from hg) hx)
  simpa only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.coe_comp,
    Function.comp_apply,projectiveRestriction] using hh

set_option backward.isDefEq.respectTransparency true

/-- The bracket on genuine structure-sheaf sections over a standard projective chart. -/
def projectiveSectionBracket
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1))
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :=
  let e := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
  e (projectiveBracket F P hF i (e.symm a) (e.symm b))

@[simp] theorem projectiveSectionBracket_equiv
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (a b : ProjectiveChartRing i) :
    projectiveSectionBracket F P hF i
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega) a)
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega) b) =
    homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
      (projectiveBracket F P hF i a b) := by
  simp only [projectiveSectionBracket,RingEquiv.symm_apply_apply]

theorem projectiveSectionBracket_skew
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1))
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :
    projectiveSectionBracket F P hF i a b = -projectiveSectionBracket F P hF i b a := by
  let e := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
  obtain ⟨x,rfl⟩ := e.surjective a
  obtain ⟨y,rfl⟩ := e.surjective b
  simp only [e,projectiveSectionBracket_equiv,projectiveBracket_skew F P hF i x y,map_neg]

theorem projectiveSectionBracket_self
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1))
    (a : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :
    projectiveSectionBracket F P hF i a a = 0 := by
  let e := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
  obtain ⟨x,rfl⟩ := e.surjective a
  have hz : projectiveBracket F P hF i x x = 0 := by
    apply HomogeneousLocalization.val_injective
    rw [projectiveBracket_val,HomogeneousLocalization.val_zero]
    exact LocalizedPoisson.bracket_self _ (contraction_skew F P) _
  simp only [e,projectiveSectionBracket_equiv,hz,map_zero]

theorem projectiveSectionBracket_add_right
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1))
    (a b c : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :
    projectiveSectionBracket F P hF i a (b+c) =
      projectiveSectionBracket F P hF i a b + projectiveSectionBracket F P hF i a c := by
  let e := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
  obtain ⟨x,rfl⟩ := e.surjective a
  obtain ⟨y,rfl⟩ := e.surjective b
  obtain ⟨z,rfl⟩ := e.surjective c
  rw [← e.map_add]
  simp only [e,projectiveSectionBracket_equiv]
  rw [projectiveBracket_add_right,map_add]

theorem projectiveSectionBracket_leibniz
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1))
    (a b c : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :
    projectiveSectionBracket F P hF i a (b*c) =
      b * projectiveSectionBracket F P hF i a c + c * projectiveSectionBracket F P hF i a b := by
  let e := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
  obtain ⟨x,rfl⟩ := e.surjective a
  obtain ⟨y,rfl⟩ := e.surjective b
  obtain ⟨z,rfl⟩ := e.surjective c
  rw [← e.map_mul]
  simp only [e,projectiveSectionBracket_equiv]
  simp only [projectiveBracket_mul_right,map_add,map_mul]

theorem projectiveSectionBracket_jacobi
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)))
    (i : Fin (n+1))
    (a b c : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :
    projectiveSectionBracket F P hF i a (projectiveSectionBracket F P hF i b c) +
    projectiveSectionBracket F P hF i b (projectiveSectionBracket F P hF i c a) +
    projectiveSectionBracket F P hF i c (projectiveSectionBracket F P hF i a b) = 0 := by
  let e := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega)
  obtain ⟨x,rfl⟩ := e.surjective a
  obtain ⟨y,rfl⟩ := e.surjective b
  obtain ⟨z,rfl⟩ := e.surjective c
  simp only [e,projectiveSectionBracket_equiv,← map_add]
  rw [projectiveBracket_jacobi F P hF hJac,map_zero]

/-- The genuine structure-sheaf restriction on a projective basic-open refinement. -/
def projectiveSectionRestriction {f g : CubicPolynomial (n+1)} (hfg : f ∣ g) :
    Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) f) →+*
      Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) g) :=
  ((ProjectiveAmbient n).presheaf.map
    (homOfLE (Proj.basicOpen_mono (homogeneousSubmodule (Fin (n+1)) ℂ) f g hfg)).op).hom

def sectionRestrictionLeft (i j : Fin (n+1)) :=
  projectiveSectionRestriction (show (X i : CubicPolynomial (n+1)) ∣ X i*X j from ⟨X j,rfl⟩)
def sectionRestrictionRight (i j : Fin (n+1)) :=
  projectiveSectionRestriction (show (X j : CubicPolynomial (n+1)) ∣ X i*X j from
    ⟨X i,mul_comm (X i) (X j)⟩)

/-- On genuine structure-sheaf sections expressed through the canonical
chart isomorphisms, the bracket is independent of the source chart on an overlap. -/
theorem projectiveSectionBracket_overlap
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i j : Fin (n+1)) (a b : ProjectiveChartRing i) (c d : ProjectiveChartRing j)
    (ha : projectiveRestriction i (isHomogeneous_X ℂ j) rfl a =
      projectiveRestriction j (isHomogeneous_X ℂ i) (mul_comm (X i) (X j)) c)
    (hb : projectiveRestriction i (isHomogeneous_X ℂ j) rfl b =
      projectiveRestriction j (isHomogeneous_X ℂ i) (mul_comm (X i) (X j)) d) :
    sectionRestrictionLeft i j (projectiveSectionBracket F P hF i
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega) a)
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) (by omega) b)) =
    sectionRestrictionRight i j (projectiveSectionBracket F P hF j
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ j) (by omega) c)
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ j) (by omega) d)) := by
  simp only [projectiveSectionBracket_equiv,sectionRestrictionLeft,sectionRestrictionRight,
    projectiveSectionRestriction]
  rw [← homogeneousSectionsEquiv_restrict i (isHomogeneous_X ℂ j) rfl
      (projectiveBracket F P hF i a b),
    ← homogeneousSectionsEquiv_restrict j (isHomogeneous_X ℂ i) (mul_comm (X i) (X j))
      (projectiveBracket F P hF j c d)]
  exact congrArg (homogeneousSectionsEquiv
    ((isHomogeneous_X ℂ i).mul (isHomogeneous_X ℂ j)) (by omega))
      (projectiveBracket_overlap F P hF i j a b c d ha hb)
end NcCubic.Geometry
