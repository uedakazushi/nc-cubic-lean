module
public import NcCubic.Geometry.HypersurfaceGlobalPoisson
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

theorem homogeneousSectionBracket_zero_trivector
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0<d) (hh : h.IsHomogeneous d) (a b) :
    HomogeneousSections.bracket (contractionCoefficients F 0)
      (contractionCoefficients_isHomogeneous F 0 hF) hd hh a b = 0 := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  rw [HomogeneousSections.bracket_equiv,← E.map_zero]
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousBasic.bracket_val,HomogeneousLocalization.val_zero]
  simp [LocalizedPoisson.bracket,contractionCoefficients,trivectorCoefficient]

theorem hypersurfaceGlobalBracket_zero_trivector
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (U : Z.Opens) (a b : Γ(Z,U)) :
    (hypersurfaceGlobalBracket ι F 0 hF hideal).bracket U a b = 0 := by
  apply (hypersurfaceBasisBracket ι F 0 hF hideal).eq_of_basis
  intro s hs
  rw [map_zero]
  apply ((hypersurfaceBasisBracket ι F 0 hF hideal).gluedBracket_restrict U a b s hs).trans
  obtain ⟨x,hx⟩ := refinementApp_surjective ι s.1 s.2.2.property ((Z.presheaf.map (homOfLE hs).op) a)
  obtain ⟨y,hy⟩ := refinementApp_surjective ι s.1 s.2.2.property ((Z.presheaf.map (homOfLE hs).op) b)
  change hypersurfaceRefinementBracket ι F 0 hF s.1 s.2.2.property _ _ = 0
  rw [← hx,← hy,hypersurfaceRefinementBracket_pullback ι F 0 hF hideal s.1 s.2.2.property]
  have hz := homogeneousSectionBracket_zero_trivector F hF (show 0<1+s.2.1 by omega)
    ((isHomogeneous_X ℂ s.1).mul s.2.2.property) x y
  change refinementApp ι s.1 (refinementAmbientBracket F 0 hF s.1 s.2.2.property x y) = 0
  exact (congrArg (refinementApp ι s.1) hz).trans (map_zero _)

theorem trivector_ne_zero_of_hypersurfaceGlobalBracket_ne_zero
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (h : ∃ (U : Z.Opens) (a b : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b ≠ 0) : P ≠ 0 := by
  rintro rfl
  obtain ⟨U,a,b,hn⟩ := h
  exact hn (hypersurfaceGlobalBracket_zero_trivector ι F hF hideal U a b)
end NcCubic.Geometry
