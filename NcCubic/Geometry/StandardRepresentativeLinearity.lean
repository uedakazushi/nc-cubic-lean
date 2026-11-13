module
public import NcCubic.Geometry.StandardRepresentativeUniqueness
public import NcCubic.Geometry.HypersurfaceGlobalRelative
@[expose] public noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 800000

/-- Genuine coefficient pullbacks commute with actual section restrictions. -/
theorem standardCoefficientMap_restrict {R : Type*} [CommRing R] {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (h : V ≤ U) (c : R) :
    X.presheaf.map (homOfLE h).op (AffineSmoothness.coefficientMap f U c) =
      AffineSmoothness.coefficientMap f V c := by
  unfold AffineSmoothness.coefficientMap
  simp only [RingHom.comp_apply]
  exact congrArg (fun g => g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    (f.appLE_map (U := ⊤) (V := U) (V' := V) le_top (homOfLE h).op)

theorem localizedBracket_smul_trivector {N : ℕ}
    (S : Submonoid (CubicPolynomial N)) (L : Type*) [CommRing L]
    [Algebra (CubicPolynomial N) L] [IsLocalization S L] [Algebra ℂ L]
    [IsScalarTower ℂ (CubicPolynomial N) L]
    (F : CubicPolynomial N) (P : Trivector N) (c : ℂ) (a b : L) :
    LocalizedPoisson.bracket S L (contractionCoefficients F (c • P)) a b =
      algebraMap (CubicPolynomial N) L (C c) *
        LocalizedPoisson.bracket S L (contractionCoefficients F P) a b := by
  have hc (i j : Fin N) : contractionCoefficients F (c • P) i j =
      C c * contractionCoefficients F P i j := by
    simp only [contractionCoefficients,trivectorCoefficient,smul_apply,smul_eq_mul,map_mul]
    simp only [Finset.mul_sum,mul_assoc]
  simp only [LocalizedPoisson.bracket,hc,map_mul,Finset.mul_sum,mul_assoc]

variable {n : ℕ} {Z : Scheme}
/-- Scalar multiplication in the original tensor is multiplication by the
actual complex coefficient section on every homogeneous ambient open. -/
theorem homogeneousSectionBracket_smul_trivector
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (P : Trivector (n+1)) (c : ℂ)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0<d) (hh : h.IsHomogeneous d) (a b) :
    HomogeneousSections.bracket (contractionCoefficients F (c • P))
      (contractionCoefficients_isHomogeneous F (c • P) hF) hd hh a b =
    AffineSmoothness.coefficientMap (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
      (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h) c *
      HomogeneousSections.bracket (contractionCoefficients F P)
        (contractionCoefficients_isHomogeneous F P hF) hd hh a b := by
  rw [homogeneous_coefficientMap_eq_constant hd hh]
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  obtain ⟨b,rfl⟩ := E.surjective b
  rw [HomogeneousSections.bracket_equiv,HomogeneousSections.bracket_equiv]
  change E _ = E (HomogeneousBasic.constant hh c) * E _
  rw [← E.map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousBasic.bracket_val,HomogeneousLocalization.val_mul,
    HomogeneousBasic.constant_val,HomogeneousBasic.bracket_val]
  exact localizedBracket_smul_trivector _ _ F P c _ _
theorem hypersurfaceRefinementBracket_smul_trivector
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (i : Fin (n+1)) {g : CubicPolynomial (n+1)} {e : ℕ} (hg : g.IsHomogeneous e)
    (c : ℂ) (a b : Γ(Z,ι ⁻¹ᵁ Proj.basicOpen
      (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g))) :
    hypersurfaceRefinementBracket ι F (c • P) hF i hg a b =
      AffineSmoothness.coefficientMap
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) _ c *
        hypersurfaceRefinementBracket ι F P hF i hg a b := by
  obtain ⟨x,rfl⟩ := refinementApp_surjective ι i hg a
  obtain ⟨y,rfl⟩ := refinementApp_surjective ι i hg b
  rw [hypersurface_coefficientMap_pullback,
    hypersurfaceRefinementBracket_pullback ι F (c • P) hF hideal i hg,
    hypersurfaceRefinementBracket_pullback ι F P hF hideal i hg,←map_mul]
  exact congrArg (refinementApp ι i)
    (homogeneousSectionBracket_smul_trivector F hF P c (show 0<1+e by omega)
      ((isHomogeneous_X ℂ i).mul hg) x y)

/-- The actual standard-representative operation depends complex-linearly on
P, using the genuine coefficient map on every section ring. -/
theorem hypersurfaceGlobalBracket_smul_trivector
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (c : ℂ) (U : Z.Opens) (a b : Γ(Z,U)) :
    (hypersurfaceGlobalBracket ι F (c • P) hF hideal).bracket U a b =
      AffineSmoothness.coefficientMap
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) U c *
        (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b := by
  apply (hypersurfaceBasisBracket ι F (c • P) hF hideal).eq_of_basis
  intro s hs
  rw [map_mul,standardCoefficientMap_restrict]
  have hd := (hypersurfaceBasisBracket ι F (c • P) hF hideal).gluedBracket_restrict U a b s hs
  have hp := (hypersurfaceBasisBracket ι F P hF hideal).gluedBracket_restrict U a b s hs
  apply hd.trans
  refine Eq.trans ?_ (congrArg (fun z =>
    AffineSmoothness.coefficientMap
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
      (subschemeRefinementOpen ι s) c * z) hp).symm
  exact hypersurfaceRefinementBracket_smul_trivector ι F P hF hideal s.1 s.2.2.property c _ _

/-- Addition also holds for the actual operation, without Jacobi assumptions. -/
theorem hypersurfaceGlobalBracket_add_trivector
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P Q : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (U : Z.Opens) (a b : Γ(Z,U)) :
    (hypersurfaceGlobalBracket ι F (P+Q) hF hideal).bracket U a b =
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b +
      (hypersurfaceGlobalBracket ι F Q hF hideal).bracket U a b := by
  have h := hypersurfaceGlobalBracket_sub_trivector ι F (P+Q) Q hF hideal U a b
  rw [add_sub_cancel_right] at h
  exact sub_eq_iff_eq_add.mp h.symm
end NcCubic.Geometry
