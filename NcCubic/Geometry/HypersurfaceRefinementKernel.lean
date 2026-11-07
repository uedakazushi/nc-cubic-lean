module
public import NcCubic.Geometry.ProjectiveHypersurfaceSections
public import NcCubic.Geometry.HomogeneousLogHamiltonian
public import NcCubic.Geometry.HomogeneousSectionBracket
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

theorem hypersurface_refinement_kernel
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1))
    {g h : CubicPolynomial (n+1)} {e : ℕ} (hg : g.IsHomogeneous e) (hx : h = X i*g) :
    RingHom.ker (ι.app (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)).hom =
      Ideal.span {(homogeneousSectionsEquiv (d:=1+e)
        (by rw [hx]; exact (isHomogeneous_X ℂ i).mul hg) (by omega)
        (HomogeneousBasic.normalizedEquation F hF i hg hx))} := by
  let 𝒜 := homogeneousSubmodule (Fin (n+1)) ℂ
  have hh : h.IsHomogeneous (1+e) := by rw [hx]; exact (isHomogeneous_X ℂ i).mul hg
  have hle : Proj.basicOpen 𝒜 h ≤ Proj.basicOpen 𝒜 (X i) := by
    rw [hx,Proj.basicOpen_mul]
    exact inf_le_left
  have hm := ι.ker.map_ideal (U:=⟨Proj.basicOpen 𝒜 h,Proj.isAffineOpen_basicOpen 𝒜 h hh (by omega)⟩)
    (V:=⟨Proj.basicOpen 𝒜 (X i),Stacks.ProjectiveChart.isAffineOpen_basicOpen_X i⟩) hle
  rw [Scheme.Hom.ker_apply,Scheme.Hom.ker_apply,
    Stacks.ProjectiveChart.ker_app_basicOpen_X_eq_span_dehomCoeff (d:=3) ℂ i ι F hF hideal,
    Ideal.map_span,Set.image_singleton] at hm
  rw [← hm]
  congr 2
  rw [Stacks.ProjectiveChart.sectionsChartEquiv_dehomCoeff ℂ i 3 F hF]
  exact (HomogeneousSections.equiv_restrict Nat.one_pos (isHomogeneous_X ℂ i) hg hx
    (projectiveEquation F hF i)).symm

/-- The actual closed-immersion kernel on every homogeneous refinement is a
Poisson ideal for the computed ambient section bracket. -/
theorem hypersurface_refinement_kernel_stable
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1))
    {g h : CubicPolynomial (n+1)} {e : ℕ} (hg : g.IsHomogeneous e) (hx : h = X i*g)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h))
    (hb : b ∈ RingHom.ker (ι.app (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)).hom) :
    HomogeneousSections.bracket (contractionCoefficients F P)
      (contractionCoefficients_isHomogeneous F P hF) (show 0 < 1+e by omega)
      (show h.IsHomogeneous (1+e) by rw [hx]; exact (isHomogeneous_X ℂ i).mul hg) a b ∈
      RingHom.ker (ι.app (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)).hom := by
  have hh : h.IsHomogeneous (1+e) := by rw [hx]; exact (isHomogeneous_X ℂ i).mul hg
  let E := homogeneousSectionsEquiv hh (show 0 < 1+e by omega)
  obtain ⟨x,rfl⟩ := E.surjective a
  obtain ⟨y,rfl⟩ := E.surjective b
  rw [hypersurface_refinement_kernel ι F hF hideal i hg hx] at hb ⊢
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hb
  have hy : y ∈ Ideal.span {HomogeneousBasic.normalizedEquation F hF i hg hx} := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨E.symm z,?_⟩
    apply E.injective
    simpa only [map_mul,RingEquiv.apply_symm_apply,E] using hz
  have hstable := HomogeneousBasic.bracket_preserves_normalizedEquationIdeal F P hF i hg hx x y hy
  rw [HomogeneousSections.bracket_equiv]
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hstable
  apply Ideal.mem_span_singleton.mpr
  exact ⟨E z,by simpa only [map_mul,E] using congrArg E hz⟩
end NcCubic.Geometry
