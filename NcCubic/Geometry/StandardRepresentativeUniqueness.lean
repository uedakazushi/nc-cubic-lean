module
public import NcCubic.Geometry.HypersurfaceBracketFaithfulness
@[expose] public noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 800000
variable {n : ℕ} {Z : Scheme}

/-- The genuine homogeneous-open operation is linear in its constant trivector. -/
theorem homogeneousSectionBracket_sub_trivector
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (P Q : Trivector (n+1))
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0<d) (hh : h.IsHomogeneous d) (a b) :
    HomogeneousSections.bracket (contractionCoefficients F (P-Q))
      (contractionCoefficients_isHomogeneous F (P-Q) hF) hd hh a b =
    HomogeneousSections.bracket (contractionCoefficients F P)
      (contractionCoefficients_isHomogeneous F P hF) hd hh a b -
    HomogeneousSections.bracket (contractionCoefficients F Q)
      (contractionCoefficients_isHomogeneous F Q hF) hd hh a b := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  rw [HomogeneousSections.bracket_equiv,HomogeneousSections.bracket_equiv,
    HomogeneousSections.bracket_equiv,← E.map_sub]
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousBasic.bracket_val,HomogeneousLocalization.val_sub,
    HomogeneousBasic.bracket_val,HomogeneousBasic.bracket_val]
  simp [LocalizedPoisson.bracket,contractionCoefficients,trivectorCoefficient,
    sub_apply,map_sub,sub_mul,Finset.sum_sub_distrib]

/-- Linearity survives the actual quotient and gluing on every hypersurface open. -/
theorem hypersurfaceGlobalBracket_sub_trivector
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P Q : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (U : Z.Opens) (a b : Γ(Z,U)) :
    (hypersurfaceGlobalBracket ι F (P-Q) hF hideal).bracket U a b =
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b -
      (hypersurfaceGlobalBracket ι F Q hF hideal).bracket U a b := by
  apply (hypersurfaceBasisBracket ι F (P-Q) hF hideal).eq_of_basis
  intro s hs
  rw [map_sub]
  have hd := (hypersurfaceBasisBracket ι F (P-Q) hF hideal).gluedBracket_restrict U a b s hs
  have hp := (hypersurfaceBasisBracket ι F P hF hideal).gluedBracket_restrict U a b s hs
  have hq := (hypersurfaceBasisBracket ι F Q hF hideal).gluedBracket_restrict U a b s hs
  apply hd.trans
  refine Eq.trans ?_ (congrArg₂ (·-·) hp hq).symm
  obtain ⟨x,hx⟩ := refinementApp_surjective ι s.1 s.2.2.property ((Z.presheaf.map (homOfLE hs).op) a)
  obtain ⟨y,hy⟩ := refinementApp_surjective ι s.1 s.2.2.property ((Z.presheaf.map (homOfLE hs).op) b)
  change hypersurfaceRefinementBracket ι F (P-Q) hF s.1 s.2.2.property _ _ =
    hypersurfaceRefinementBracket ι F P hF s.1 s.2.2.property _ _ -
      hypersurfaceRefinementBracket ι F Q hF s.1 s.2.2.property _ _
  rw [←hx,←hy,hypersurfaceRefinementBracket_pullback ι F (P-Q) hF hideal s.1 s.2.2.property,
    hypersurfaceRefinementBracket_pullback ι F P hF hideal s.1 s.2.2.property,
    hypersurfaceRefinementBracket_pullback ι F Q hF hideal s.1 s.2.2.property]
  rw [←map_sub]
  exact congrArg (refinementApp ι s.1)
    (homogeneousSectionBracket_sub_trivector F hF P Q (show 0<1+s.2.1 by omega)
      ((isHomogeneous_X ℂ s.1).mul s.2.2.property) x y)

/-- Constant trivector representatives of the actual hypersurface operation
are unique on every smooth cubic in the theorem's dimension range. -/
theorem hypersurfaceGlobalBracket_injective
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    Function.Injective (fun P : Trivector (n+1) => hypersurfaceGlobalBracket ι F P hF hideal) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply (hypersurfaceGlobalBracket_zero_iff ι hN F hF0 (P-Q) hF hgrad hideal).mp
  intro U a b
  rw [hypersurfaceGlobalBracket_sub_trivector]
  exact sub_eq_zero.mpr (congrArg (fun B => B.bracket U a b) hPQ)
/-- Equality of the actual operations on all opens already forces equality
of the constant trivectors; no equality of presentation data is required. -/
theorem trivector_eq_of_hypersurfaceGlobalBracket_eq
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (P Q : Trivector (n+1))
    (hPQ : ∀ (U : Z.Opens) (a b : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b =
        (hypersurfaceGlobalBracket ι F Q hF hideal).bracket U a b) : P = Q := by
  apply sub_eq_zero.mp
  apply (hypersurfaceGlobalBracket_zero_iff ι hN F hF0 (P-Q) hF hgrad hideal).mp
  intro U a b
  rw [hypersurfaceGlobalBracket_sub_trivector]
  exact sub_eq_zero.mpr (hPQ U a b)
end NcCubic.Geometry
