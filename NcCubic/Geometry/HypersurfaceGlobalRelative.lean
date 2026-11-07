module
public import NcCubic.Geometry.HypersurfaceGlobalPoisson
public import NcCubic.Geometry.AmbientProjectiveRelative
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

theorem hypersurface_coefficientMap_pullback
    (ι : Z ⟶ ProjectiveAmbient n) (U : (ProjectiveAmbient n).Opens) (c : ℂ) :
    AffineSmoothness.coefficientMap
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) (ι ⁻¹ᵁ U) c =
    (ι.app U).hom (AffineSmoothness.coefficientMap
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) U c) := by
  have h : (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n).appLE ⊤ U le_top ≫
      ι.app U = (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n).appLE ⊤
        (ι ⁻¹ᵁ U) le_top := by
    rw [← ι.appLE_eq_app]
    exact Scheme.Hom.appLE_comp_appLE ι _ _ _ _ _ _
  exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) h).symm

theorem hypersurfaceRefinementBracket_constant_right
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (i : Fin (n+1)) {g : CubicPolynomial (n+1)} {e : ℕ} (hg : g.IsHomogeneous e)
    (a : Γ(Z,ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g))) (c : ℂ) :
    hypersurfaceRefinementBracket ι F P hF i hg a
      (AffineSmoothness.coefficientMap
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) _ c) = 0 := by
  obtain ⟨x,rfl⟩ := refinementApp_surjective ι i hg a
  rw [hypersurface_coefficientMap_pullback,
    hypersurfaceRefinementBracket_pullback ι F P hF hideal i hg]
  have hzero : refinementAmbientBracket F P hF i hg x
      (AffineSmoothness.coefficientMap
        (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) _ c) = 0 := by
    rw [homogeneous_coefficientMap_eq_constant (show 0<1+e by omega)
      ((isHomogeneous_X ℂ i).mul hg)]
    exact HomogeneousSections.bracket_constant_right _ _ _ _ x c
  rw [hzero,map_zero]

theorem hypersurfaceGlobalPoisson_relative
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P))) :
    (hypersurfaceGlobalPoisson ι F P hF hideal hJac).IsRelative
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) := by
  apply (hypersurfaceBasisPoisson ι F P hF hideal hJac).glued_relative
  intro s a c
  exact hypersurfaceRefinementBracket_constant_right ι F P hF hideal s.1 s.2.2.property a c
end NcCubic.Geometry
