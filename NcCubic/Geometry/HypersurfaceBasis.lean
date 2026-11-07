/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.AmbientProjectivePoisson
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}
/-- Positive homogeneous refinements inside a chosen standard coordinate chart. -/
abbrev ProjectiveRefinementIndex (n : ℕ) :=
  Σ _i : Fin (n+1), Σ d : ℕ, homogeneousSubmodule (Fin (n+1)) ℂ d

def projectiveRefinementOpen (s : ProjectiveRefinementIndex n) : (ProjectiveAmbient n).Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) ((X s.1 : CubicPolynomial (n+1)) * (s.2.2 : CubicPolynomial (n+1)))

def subschemeRefinementOpen {Z : Scheme} (ι : Z ⟶ ProjectiveAmbient n)
    (s : ProjectiveRefinementIndex n) : Z.Opens := ι ⁻¹ᵁ projectiveRefinementOpen s


/-- Each refinement lies in its designated standard coordinate chart. -/
theorem projectiveRefinementOpen_le (s : ProjectiveRefinementIndex n) :
    projectiveRefinementOpen s ≤ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X s.1) :=
  Proj.basicOpen_mono _ _ _ ⟨(s.2.2 : CubicPolynomial (n+1)),rfl⟩

/-- Every positive homogeneous refinement is an actual affine open. -/
theorem isAffineOpen_projectiveRefinement (s : ProjectiveRefinementIndex n) :
    IsAffineOpen (projectiveRefinementOpen s) :=
  Proj.isAffineOpen_basicOpen _ _
    ((isHomogeneous_X ℂ s.1).mul s.2.2.property) (by omega)

/-- Closed-subscheme refinements are actual affine opens as well. -/
theorem isAffineOpen_subschemeRefinement {Z : Scheme}
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι] (s : ProjectiveRefinementIndex n) :
    IsAffineOpen (subschemeRefinementOpen ι s) :=
  (isAffineOpen_projectiveRefinement s).preimage ι

/-- Every open of an actual closed subscheme is an ambient open preimage. -/
theorem exists_ambient_open_of_closedImmersion {Z : Scheme}
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι] (U : Z.Opens) :
    ∃ V : (ProjectiveAmbient n).Opens, ι ⁻¹ᵁ V = U := by
  obtain ⟨V,hV,hVU⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.mp U.isOpen
  exact ⟨⟨V,hV⟩,TopologicalSpace.Opens.ext hVU⟩

/-- Standard-chart homogeneous refinements form a basis on every actual
closed subscheme, rather than merely covering the whole scheme. -/
theorem subschemeRefinementOpen_cover {Z : Scheme}
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι] (U : Z.Opens) :
    U ≤ ⨆ s : {s : ProjectiveRefinementIndex n // subschemeRefinementOpen ι s ≤ U},
      subschemeRefinementOpen ι s.val := by
  obtain ⟨V,rfl⟩ := exists_ambient_open_of_closedImmersion ι U
  intro x hx
  obtain ⟨d,g,hd,hg,hxg,hgV⟩ :=
    Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le
      (homogeneousSubmodule (Fin (n+1)) ℂ) hx
  have hxall : ι x ∈ (⨆ i : Fin (n+1),
      Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)) := by
    rw [Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top]
    trivial
  obtain ⟨i,hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxall
  let s : ProjectiveRefinementIndex n := ⟨i,d,g,hg⟩
  have hs : subschemeRefinementOpen ι s ≤ ι ⁻¹ᵁ V := by
    change ι ⁻¹ᵁ Proj.basicOpen _ (X i*g) ≤ _
    rw [Proj.basicOpen_mul]
    exact fun z hz => hgV hz.2
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨s,hs⟩,?_⟩
  change ι x ∈ Proj.basicOpen _ (X i*g)
  rw [Proj.basicOpen_mul]
  exact ⟨hxi,hxg⟩
end NcCubic.Geometry
