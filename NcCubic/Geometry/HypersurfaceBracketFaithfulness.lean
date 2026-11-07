module
public import NcCubic.Geometry.HypersurfaceBracketInjective
public import NcCubic.Geometry.HypersurfaceBracketZero
public import NcCubic.Geometry.RepresentativeFaithfulness
@[expose] public section
noncomputable section

namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

theorem hypersurfaceGlobalBracket_zero_iff
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    (∀ (U : Z.Opens) (a b : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b = 0) ↔ P = 0 := by
  constructor
  · intro hzero
    exact trivector_zero_of_euler_coefficients_divisible hN F hF0 hF hgrad P
      (eulerWedge2_divisible_of_hypersurfaceGlobalBracket_zero ι F P hF hideal hzero)
  · rintro rfl
    exact hypersurfaceGlobalBracket_zero_trivector ι F hF hideal

theorem hypersurfaceGlobalBracket_nonzero_iff
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    (∃ (U : Z.Opens) (a b : Γ(Z,U)),
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b ≠ 0) ↔ P ≠ 0 := by
  simpa only [not_forall] using not_congr (hypersurfaceGlobalBracket_zero_iff ι hN F hF0 P hF hgrad hideal)
end NcCubic.Geometry
