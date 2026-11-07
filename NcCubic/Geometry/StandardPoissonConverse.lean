/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.StandardBracketClassification
public import NcCubic.Geometry.HypersurfaceBracketFaithfulness
public import NcCubic.BlockNonzero
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}
/-- Block normal form constructs a nonzero relative Poisson operation on the
actual hypersurface structure sheaf. Its realization as an actual bivector is a
separate comparison, not assumed here. -/
theorem exists_nonzero_standardPoisson_of_normalForm
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hNF : HasBlockNormalForm F P) :
    ∃ B : StructureSheafPoisson Z,
      B.IsRelative (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) ∧
      (∀ (U : Z.Opens) (a b : Γ(Z,U)), B.bracket U a b =
        (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b) ∧
      ∃ (U : Z.Opens) (a b : Γ(Z,U)), B.bracket U a b ≠ 0 := by
  have hJac := normalForm_satisfiesJacobi F P hNF
  refine ⟨hypersurfaceGlobalPoisson ι F P hF hideal hJac,
    hypersurfaceGlobalPoisson_relative ι F P hF hideal hJac,?_,?_⟩
  · intro U a b
    rfl
  · have hgrad := ChartComparison.isolated_gradient_of_scheme_smooth ι F hF hF0 hideal
    exact (hypersurfaceGlobalBracket_nonzero_iff ι hN F hF0 P hF hgrad hideal).2
      (normalForm_trivector_ne_zero hNF)
end NcCubic.Geometry
