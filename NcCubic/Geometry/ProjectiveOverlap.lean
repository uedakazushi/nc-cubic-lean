/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.ProjectivePoisson
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The genuine restriction between homogeneous degree-zero localizations
on a projective basic-open refinement. -/
def projectiveRestriction (i : Fin (n+1)) {d : ℕ}
    {g x : CubicPolynomial (n+1)} (hg : g.IsHomogeneous d) (hx : x = X i*g) :
    ProjectiveChartRing i →+*
      HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n+1)) ℂ) x :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin (n+1)) ℂ) hg hx

/-- The ambient localization transition underlying the actual homogeneous
restriction. -/
def chartLocalizationRestriction (i : Fin (n+1))
    {g x : CubicPolynomial (n+1)} (hx : x = X i*g) :
    ChartLocalization i →ₐ[CubicPolynomial (n+1)] Localization.Away x :=
  IsLocalization.Away.liftAlgHom (f := Algebra.ofId (CubicPolynomial (n+1)) (Localization.Away x))
    (X i) (isUnit_of_dvd_unit (map_dvd _ ⟨g,hx⟩)
      (IsLocalization.Away.algebraMap_isUnit x))

theorem projectiveRestriction_val (i : Fin (n+1)) {d : ℕ}
    {g x : CubicPolynomial (n+1)} (hg : g.IsHomogeneous d) (hx : x = X i*g)
    (a : ProjectiveChartRing i) :
    (projectiveRestriction i hg hx a).val = chartLocalizationRestriction i hx a.val := by
  exact (HomogeneousLocalization.val_awayMap
    (homogeneousSubmodule (Fin (n+1)) ℂ)
    (show g ∈ homogeneousSubmodule (Fin (n+1)) ℂ d from hg) hx a).trans (by rfl)

/-- The actual projective restriction map intertwines the bracket with
its canonical localization on every basic-open overlap. -/
theorem projectiveBracket_restriction
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) {d : ℕ} {g x : CubicPolynomial (n+1)}
    (hg : g.IsHomogeneous d) (hx : x = X i*g) (a b : ProjectiveChartRing i) :
    (projectiveRestriction i hg hx (projectiveBracket F P hF i a b)).val =
    LocalizedPoisson.bracket (Submonoid.powers x) (Localization.Away x)
      (contractionCoefficients F P) (projectiveRestriction i hg hx a).val
        (projectiveRestriction i hg hx b).val := by
  simp only [projectiveRestriction_val,projectiveBracket_val]
  exact LocalizedPoisson.bracket_natural _ (chartLocalizationRestriction i hx) a.val b.val

/-- On a genuine intersection D₊(z_i z_j), equal restricted functions
have equal restricted brackets, independently of their source chart. -/
theorem projectiveBracket_overlap
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i j : Fin (n+1)) (a b : ProjectiveChartRing i) (c d : ProjectiveChartRing j)
    (ha : projectiveRestriction i (isHomogeneous_X ℂ j) rfl a =
      projectiveRestriction j (isHomogeneous_X ℂ i) (mul_comm (X i) (X j)) c)
    (hb : projectiveRestriction i (isHomogeneous_X ℂ j) rfl b =
      projectiveRestriction j (isHomogeneous_X ℂ i) (mul_comm (X i) (X j)) d) :
    projectiveRestriction i (isHomogeneous_X ℂ j) rfl (projectiveBracket F P hF i a b) =
      projectiveRestriction j (isHomogeneous_X ℂ i) (mul_comm (X i) (X j))
        (projectiveBracket F P hF j c d) := by
  apply HomogeneousLocalization.val_injective
  rw [projectiveBracket_restriction,projectiveBracket_restriction,ha,hb]
end NcCubic.Geometry
