/- Classification of the actual structure-sheaf brackets of standard representatives.
This does not assert that every geometric bivector has such a representative. -/
module
public import NcCubic.AffineClassification
public import NcCubic.Geometry.HypersurfaceStandardComparison
public import NcCubic.Geometry.HypersurfaceBracketZero
public import NcCubic.Geometry.ChartComparison
@[expose] public noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

/-- For an actual smooth projective cubic, Jacobi for the every-open bracket of
an explicitly given nonzero standard representative is exactly block normal form.
Existence of a representative for an arbitrary bivector is a separate theorem. -/
theorem standardBracketJacobi_iff_blockNormalForm
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hP : P ≠ 0) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    (∀ (U : Z.Opens) (a b c : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a
        ((hypersurfaceGlobalBracket ι F P hF hideal).bracket U b c) +
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U b
        ((hypersurfaceGlobalBracket ι F P hF hideal).bracket U c a) +
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U c
        ((hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b) = 0) ↔
      HasBlockNormalForm F P := by
  have hgrad := ChartComparison.isolated_gradient_of_scheme_smooth ι F hF hF0 hideal
  exact (polynomialJacobi_iff_hypersurfaceGlobalJacobi ι hN F hF0 P hF hgrad hideal).symm.trans
    (theorem113_affine (n+1) hN F P hF0 hF hgrad hP)

end NcCubic.Geometry
