/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.HomogeneousBasicBracket
public import NcCubic.Geometry.ProjectiveSectionBracket
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace NcCubic.Geometry.HomogeneousSections
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 600000
variable {n : ℕ}

/-- The canonical homogeneous-basic-open bracket acts on genuine structure-sheaf sections. -/
def bracket (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :=
  let e := homogeneousSectionsEquiv hh hd
  e (HomogeneousBasic.bracket q hq hd hh (e.symm a) (e.symm b))

@[simp] theorem bracket_equiv
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a b : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n+1)) ℂ) h) :
    bracket q hq hd hh (homogeneousSectionsEquiv hh hd a) (homogeneousSectionsEquiv hh hd b) =
      homogeneousSectionsEquiv hh hd (HomogeneousBasic.bracket q hq hd hh a b) := by
  simp only [bracket,RingEquiv.symm_apply_apply]

/-- The exact scheme-section restriction diagram for every homogeneous refinement. -/
theorem equiv_restrict
    {f g x : CubicPolynomial (n+1)} {d e : ℕ}
    (hd : 0 < d) (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hx : x=f*g)
    (a : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n+1)) ℂ) f) :
    homogeneousSectionsEquiv (hx ▸ hf.mul hg) (by omega)
        (HomogeneousBasic.restriction hg hx a) =
      projectiveSectionRestriction (show f ∣ x from ⟨g,hx⟩) (homogeneousSectionsEquiv hf hd a) := by
  simp only [homogeneousSectionsEquiv_apply]
  have hh := congrArg
    (fun φ : CommRingCat.of (HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n+1)) ℂ) f) ⟶
      Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) x) => φ.hom a)
    (Proj.awayMap_awayToSection (homogeneousSubmodule (Fin (n+1)) ℂ)
      (show g ∈ homogeneousSubmodule (Fin (n+1)) ℂ e from hg) hx)
  simpa only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.coe_comp,
    Function.comp_apply,HomogeneousBasic.restriction,projectiveSectionRestriction] using hh

/-- Naturality on genuine structure-sheaf sections over all positive
homogeneous basic opens, including all product refinements. -/
theorem bracket_restrict
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {f g x : CubicPolynomial (n+1)} {d e : ℕ}
    (hd : 0 < d) (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hx : x=f*g)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) f)) :
    projectiveSectionRestriction (show f ∣ x from ⟨g,hx⟩) (bracket q hq hd hf a b) =
      bracket q hq (by omega : 0 < d+e) (hx ▸ hf.mul hg)
        (projectiveSectionRestriction (show f ∣ x from ⟨g,hx⟩) a)
        (projectiveSectionRestriction (show f ∣ x from ⟨g,hx⟩) b) := by
  let E := homogeneousSectionsEquiv hf hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  simp only [E,bracket_equiv]
  rw [← equiv_restrict hd hf hg hx (HomogeneousBasic.bracket q hq hd hf a b),
    ← equiv_restrict hd hf hg hx a,← equiv_restrict hd hf hg hx b,bracket_equiv]
  exact congrArg (homogeneousSectionsEquiv (hx ▸ hf.mul hg) (by omega))
    (HomogeneousBasic.bracket_restriction q hq hd hf hg hx a b)

/-- The actual section operation is independent of the choice of positive
homogeneous degree witnessing the same basic-open equation. -/
theorem bracket_independent
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial (n+1)} {d e : ℕ}
    (hd : 0 < d) (hh : h.IsHomogeneous d) (he : 0 < e) (hh' : h.IsHomogeneous e)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    bracket q hq hd hh a b = bracket q hq he hh' a b := by
  have hE : homogeneousSectionsEquiv hh hd = homogeneousSectionsEquiv hh' he := by
    apply RingEquiv.ext
    intro x
    simp only [homogeneousSectionsEquiv_apply]
  unfold bracket
  rw [hE]
  apply congrArg (homogeneousSectionsEquiv hh' he)
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousBasic.bracket_val]

/-- Naturality with any chosen positive homogeneous witness on the target
basic open; convenient for a basis whose intersection index is fixed. -/
theorem bracket_restrict_any
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {f g x : CubicPolynomial (n+1)} {d e r : ℕ}
    (hd : 0 < d) (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hx : x=f*g)
    (hr : 0 < r) (hxhom : x.IsHomogeneous r)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) f)) :
    projectiveSectionRestriction (show f ∣ x from ⟨g,hx⟩) (bracket q hq hd hf a b) =
      bracket q hq hr hxhom
        (projectiveSectionRestriction (show f ∣ x from ⟨g,hx⟩) a)
        (projectiveSectionRestriction (show f ∣ x from ⟨g,hx⟩) b) :=
  (bracket_restrict q hq hd hf hg hx a b).trans
    (bracket_independent q hq (by omega) (hx ▸ hf.mul hg) hr hxhom _ _)

/-- The actual intersection agreement for any pair of positive homogeneous
basic opens, expressed on D₊(fg)=D₊(f)∩D₊(g). -/
theorem bracket_overlap
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {f g : CubicPolynomial (n+1)} {d e : ℕ}
    (hd : 0 < d) (hf : f.IsHomogeneous d) (he : 0 < e) (hg : g.IsHomogeneous e)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) f))
    (c z : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) g))
    (ha : projectiveSectionRestriction (show f ∣ f*g from ⟨g,rfl⟩) a =
      projectiveSectionRestriction (show g ∣ f*g from ⟨f,mul_comm f g⟩) c)
    (hb : projectiveSectionRestriction (show f ∣ f*g from ⟨g,rfl⟩) b =
      projectiveSectionRestriction (show g ∣ f*g from ⟨f,mul_comm f g⟩) z) :
    projectiveSectionRestriction (show f ∣ f*g from ⟨g,rfl⟩) (bracket q hq hd hf a b) =
      projectiveSectionRestriction (show g ∣ f*g from ⟨f,mul_comm f g⟩) (bracket q hq he hg c z) := by
  rw [bracket_restrict_any q hq hd hf hg rfl (by omega) (hf.mul hg),
    bracket_restrict_any q hq he hg hf (mul_comm f g) (by omega) (hf.mul hg),ha,hb]

/-- Alternation holds on every genuine positive homogeneous basic-open section ring. -/
theorem bracket_self
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    (hskew : ∀ i j,q j i = -q i j)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    bracket q hq hd hh a a = 0 := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  simp only [E,bracket_equiv,HomogeneousBasic.bracket_self q hq hskew hd hh,map_zero]

theorem bracket_skew
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    (hskew : ∀ i j,q j i = -q i j)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    bracket q hq hd hh a b = -bracket q hq hd hh b a := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  simp only [E,bracket_equiv,HomogeneousBasic.bracket_skew q hq hskew hd hh a b,map_neg]

theorem bracket_add_right
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a b c : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    bracket q hq hd hh a (b+c) = bracket q hq hd hh a b + bracket q hq hd hh a c := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  obtain ⟨c,rfl⟩ := E.surjective c
  rw [← E.map_add]
  simp only [E,bracket_equiv]
  rw [HomogeneousBasic.bracket_add_right,map_add]

theorem bracket_leibniz
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a b c : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    bracket q hq hd hh a (b*c) = b*bracket q hq hd hh a c + c*bracket q hq hd hh a b := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  obtain ⟨c,rfl⟩ := E.surjective c
  rw [← E.map_mul]
  simp only [E,bracket_equiv]
  simp only [HomogeneousBasic.bracket_leibniz,map_add,map_mul]

theorem bracket_jacobi
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    (hskew : ∀ i j,q j i = -q i j) (hJac : SatisfiesJacobi (bracketFromCoefficients q))
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a b c : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    bracket q hq hd hh a (bracket q hq hd hh b c) +
    bracket q hq hd hh b (bracket q hq hd hh c a) +
    bracket q hq hd hh c (bracket q hq hd hh a b) = 0 := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  obtain ⟨c,rfl⟩ := E.surjective c
  simp only [E,bracket_equiv,← map_add]
  rw [HomogeneousBasic.bracket_jacobi q hq hskew hJac,map_zero]
end NcCubic.Geometry.HomogeneousSections
