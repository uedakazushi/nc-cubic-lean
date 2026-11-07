module
public import NcCubic.Geometry.HypersurfaceRefinementBracket
public import NcCubic.Geometry.HomogeneousSectionNaturality
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

theorem hypersurfaceRefinementBracket_restrict
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (i j : Fin (n+1)) {g k : CubicPolynomial (n+1)} {e d : ℕ}
    (hg : g.IsHomogeneous e) (hk : k.IsHomogeneous d)
    (h : Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X j*k) ≤
      Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g))
    (a b : Γ(Z,ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g))) :
    (Z.presheaf.map (homOfLE (show ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X j*k) ≤
      ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g) from fun _ hx => h hx)).op)
      (hypersurfaceRefinementBracket ι F P hF i hg a b) =
    hypersurfaceRefinementBracket ι F P hF j hk
      ((Z.presheaf.map (homOfLE (show ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X j*k) ≤
        ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g) from fun _ hx => h hx)).op) a)
      ((Z.presheaf.map (homOfLE (show ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X j*k) ≤
        ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g) from fun _ hx => h hx)).op) b) := by
  apply BracketDescent.operation_natural
    (refinementApp ι i) (refinementApp_surjective ι i hg) _
    (fun ha hb => refinementAmbientBracket_congr ι F P hF hideal i hg ha hb)
    (refinementApp ι j) (refinementApp_surjective ι j hk) _
    (fun ha hb => refinementAmbientBracket_congr ι F P hF hideal j hk ha hb)
    (((ProjectiveAmbient n).presheaf.map (homOfLE h).op).hom)
    ((Z.presheaf.map (homOfLE (show ι ⁻¹ᵁ _ ≤ ι ⁻¹ᵁ _ from fun _ hx => h hx)).op).hom)
  · intro x
    have hh := congrArg (fun φ => φ.hom x) (ι.naturality (homOfLE h).op)
    exact hh.symm
  · intro x y
    exact homogeneousSectionBracket_restrict_le _ _ (by omega)
      ((isHomogeneous_X ℂ i).mul hg) (by omega) ((isHomogeneous_X ℂ j).mul hk) h x y
end NcCubic.Geometry
