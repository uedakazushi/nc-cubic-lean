/- Canonical hypersurface construction generalized from pinned Stacks
StacksFrontier.AlgebraicGeometry.Curves.Models.PlaneCurveModel.
The ideal computation uses ProjSaturation.VPlus (Tag 0BXK) and our
unconditional two-variable principal-ideal saturation lemma. -/
module
public import NcCubic.Geometry.PrincipalSaturation
public import NcCubic.Geometry.ChartComparison
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.VPlus
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.CanonicalHypersurface
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R : Type u} [CommRing R] {σ : Type u}
/-- The actual homogeneous principal equation ideal. -/
def equationIdeal (F : MvPolynomial σ R) {d : ℕ} (hF : F.IsHomogeneous d) :
    HomogeneousIdeal (homogeneousSubmodule σ R) where
  toSubmodule := Ideal.span {F}
  is_homogeneous' := Ideal.homogeneous_span _ _ <| by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨d, hx ▸ (mem_homogeneousSubmodule d F).2 hF⟩
abbrev grading (F : MvPolynomial σ R) {d : ℕ} (hF : F.IsHomogeneous d) :=
  Stacks.HomogeneousIdeal.quotientGrading (equationIdeal F hF)
abbrev scheme (F : MvPolynomial σ R) {d : ℕ} (hF : F.IsHomogeneous d) : Scheme.{u} :=
  Proj (grading F hF)
def embedding (F : MvPolynomial σ R) {d : ℕ} (hF : F.IsHomogeneous d) :
    scheme F hF ⟶ Proj (homogeneousSubmodule σ R) :=
  Proj.map (Stacks.HomogeneousIdeal.quotientMk (equationIdeal F hF))
    (Proj.irrelevant_le_map_of_surjective _ (Stacks.HomogeneousIdeal.surjective_quotientMk _))
instance (F : MvPolynomial σ R) {d : ℕ} (hF : F.IsHomogeneous d) :
    IsClosedImmersion (embedding F hF) := Proj.isClosedImmersion_map_quotientMk _

variable {K : Type u} [Field K] [Finite σ]
theorem idealOfClosedSubscheme_embedding (F : MvPolynomial σ K) {d : ℕ}
    (hF : F.IsHomogeneous d) (i j : σ) (hij : i ≠ j) :
    ProjectiveSpectrum.Proj.idealOfClosedSubscheme (homogeneousSubmodule σ K)
      (embedding F hF) = Ideal.span {F} := by
  refine ProjectiveSpectrum.Proj.idealOfClosedSubscheme_projMap_quotientMk_eq
    _ (equationIdeal F hF) _ (adjoin_homogeneousSubmodule_one_eq_top σ K) ?_
  intro p hp
  apply PrincipalSaturation.principal_homogeneous_saturated i j hij F p
  obtain ⟨N,hN⟩ := hp
  exact ⟨N, fun y hy => hN y ((mem_homogeneousSubmodule N y).2 hy)⟩
/-- The canonical projective cubic has no extra defining-ideal hypothesis:
smoothness is exactly isolated vanishing of its homogeneous gradient. -/
theorem smooth_iff_isolated_gradient {n : ℕ} (F : CubicPolynomial (n+2))
    (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) :
    Smooth (embedding F hF ≫
      Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ (n+1)) ↔
      HasIsolatedGradientZero F := by
  apply ChartComparison.scheme_smooth_iff_isolated_gradient
    (embedding F hF) F hF hF0
  apply idealOfClosedSubscheme_embedding F hF (0 : Fin (n+2)) 1
  exact Fin.zero_ne_one

end NcCubic.Geometry.CanonicalHypersurface
