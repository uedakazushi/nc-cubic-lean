module
public import NcCubic.Geometry.HypersurfaceGlobalRelative
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

theorem homogeneousSectionBracket_standard
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (i : Fin (n+1)) (a b) :
    HomogeneousSections.bracket (contractionCoefficients F P)
      (contractionCoefficients_isHomogeneous F P hF) Nat.one_pos (isHomogeneous_X ℂ i) a b =
      projectiveSectionBracket F P hF i a b := by
  let E := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos
  obtain ⟨x,rfl⟩ := E.surjective a
  obtain ⟨y,rfl⟩ := E.surjective b
  rw [HomogeneousSections.bracket_equiv,projectiveSectionBracket_equiv]
  congr 1

theorem hypersurfaceGlobalBracket_basic
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (s : ProjectiveRefinementIndex n) (a b : Γ(Z,subschemeRefinementOpen ι s)) :
    (hypersurfaceGlobalBracket ι F P hF hideal).bracket _ a b =
      hypersurfaceRefinementBracket ι F P hF s.1 s.2.2.property a b := by
  have ht := (hypersurfaceBasisBracket ι F P hF hideal).gluedBracket_restrict _ a b s le_rfl
  have hid : (homOfLE (le_refl (subschemeRefinementOpen ι s))).op =
      𝟙 (Opposite.op (subschemeRefinementOpen ι s)) := rfl
  rw [hid,CategoryTheory.Functor.map_id] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
theorem hypersurfaceGlobalBracket_standard_pullback
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (i : Fin (n+1))
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :
    (hypersurfaceGlobalBracket ι F P hF hideal).bracket _ ((ι.app _).hom a) ((ι.app _).hom b) =
      (ι.app _).hom (projectiveSectionBracket F P hF i a b) := by
  let s : ProjectiveRefinementIndex n := ⟨i,0,1,isHomogeneous_one _ _⟩
  let U := Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)
  let V := projectiveRefinementOpen s
  have hVU : V ≤ U := projectiveRefinementOpen_le s
  have hUV : U ≤ V := by simp [U,V,s,projectiveRefinementOpen]
  have hZVU : ι ⁻¹ᵁ V ≤ ι ⁻¹ᵁ U := fun _ hx => hVU hx
  have hZUV : ι ⁻¹ᵁ U ≤ ι ⁻¹ᵁ V := fun _ hx => hUV hx
  have hmap (x : Γ(ProjectiveAmbient n,U)) :
      (Z.presheaf.map (homOfLE hZVU).op) ((ι.app U).hom x) =
      (ι.app V).hom (((ProjectiveAmbient n).presheaf.map (homOfLE hVU).op) x) := by
    exact (congrArg (fun φ => φ.hom x) (ι.naturality (homOfLE hVU).op)).symm
  have hr : (Z.presheaf.map (homOfLE hZVU).op)
      ((hypersurfaceGlobalBracket ι F P hF hideal).bracket _ ((ι.app U).hom a) ((ι.app U).hom b)) =
      (Z.presheaf.map (homOfLE hZVU).op) ((ι.app U).hom (projectiveSectionBracket F P hF i a b)) := by
    have hbV (x y : Γ(Z,ι ⁻¹ᵁ V)) :
        (hypersurfaceGlobalBracket ι F P hF hideal).bracket _ x y =
          hypersurfaceRefinementBracket ι F P hF s.1 s.2.2.property x y :=
      hypersurfaceGlobalBracket_basic ι F P hF hideal s x y
    rw [(hypersurfaceGlobalBracket ι F P hF hideal).restrict,hbV,hmap,hmap,hmap]
    apply (hypersurfaceRefinementBracket_pullback ι F P hF hideal s.1 s.2.2.property _ _).trans
    apply congrArg (ι.app V).hom
    exact (homogeneousSectionBracket_restrict_le _ _ Nat.one_pos (isHomogeneous_X ℂ i)
      (show 0<1+s.2.1 by omega) ((isHomogeneous_X ℂ s.1).mul s.2.2.property) hVU a b).symm.trans
      (congrArg (((ProjectiveAmbient n).presheaf.map (homOfLE hVU).op).hom)
        (homogeneousSectionBracket_standard F P hF i a b))
  have hh := congrArg (fun z => (Z.presheaf.map (homOfLE hZUV).op) z) hr
  have hcomp (x : Γ(Z,ι ⁻¹ᵁ U)) :
      (Z.presheaf.map (homOfLE hZUV).op) ((Z.presheaf.map (homOfLE hZVU).op) x) = x := by
    rw [← ConcreteCategory.comp_apply,← CategoryTheory.Functor.map_comp]
    have hid : (homOfLE hZVU).op ≫ (homOfLE hZUV).op = 𝟙 (Opposite.op (ι ⁻¹ᵁ U)) := Subsingleton.elim _ _
    rw [hid,CategoryTheory.Functor.map_id]
    rfl
  simpa only [hcomp] using hh

theorem hypersurfaceGlobalBracket_standard
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (i : Fin (n+1)) (a b : Γ(Z,Stacks.ProjectiveChart.subschemeChart ι i)) :
    (hypersurfaceGlobalBracket ι F P hF hideal).bracket _ a b =
      hypersurfaceSectionBracket ι F P hF hideal i a b := by
  obtain ⟨a,rfl⟩ := ι.app_surjective _ (Stacks.ProjectiveChart.isAffineOpen_basicOpen_X i) a
  obtain ⟨b,rfl⟩ := ι.app_surjective _ (Stacks.ProjectiveChart.isAffineOpen_basicOpen_X i) b
  rw [hypersurfaceGlobalBracket_standard_pullback,hypersurfaceSectionBracket_pullback]

/-- The actual every-open hypersurface operation is Jacobi exactly when the
original polynomial contraction is Jacobi. -/
theorem polynomialJacobi_iff_hypersurfaceGlobalJacobi
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) ↔
      ∀ (U : Z.Opens) (a b c : Γ(Z,U)),
        (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a
          ((hypersurfaceGlobalBracket ι F P hF hideal).bracket U b c) +
        (hypersurfaceGlobalBracket ι F P hF hideal).bracket U b
          ((hypersurfaceGlobalBracket ι F P hF hideal).bracket U c a) +
        (hypersurfaceGlobalBracket ι F P hF hideal).bracket U c
          ((hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b) = 0 := by
  constructor
  · intro hJac U a b c
    exact (hypersurfaceGlobalPoisson ι F P hF hideal hJac).jacobi U a b c
  · intro hJac
    apply polynomialJacobi_of_hypersurfaceSectionJacobi ι hN F hF0 P hF hgrad hideal
    intro i a b c
    simpa only [← hypersurfaceGlobalBracket_standard ι F P hF hideal i] using hJac _ a b c
end NcCubic.Geometry
