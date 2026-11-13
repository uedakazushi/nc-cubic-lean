/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.HypersurfaceBivector
public import NcCubic.Geometry.BivectorFaithfulnessCanonical
public import NcCubic.Geometry.BivectorCoefficientLinearity
public import NcCubic.Geometry.StandardRepresentativeLinearity
public import NcCubic.Geometry.StandardRepresentativeUniqueness
public import NcCubic.Geometry.ChartComparison
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
variable (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
  [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
  (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
  (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
    (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
local notation "g" => ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n
/-- The actual constant-trivector realization is complex-linear for the
coefficient action induced by the actual structure morphism. -/
def hypersurfaceBivectorLinear : Trivector (n+1) →ₗ[ℂ] bivectorCoefficientSections g where
  toFun P := hypersurfaceBivector ι F P hF hideal
  map_add' P Q := by
    apply algebraicBivectorBracket_ext_smooth g
    intro U a b
    exact (hypersurfaceBivector_standardRepresentative ι F (P+Q) hF hideal U a b).trans
      ((hypersurfaceGlobalBracket_add_trivector ι F P Q hF hideal U a b).trans
        ((congrArg₂ (·+·)
          (hypersurfaceBivector_standardRepresentative ι F P hF hideal U a b).symm
          (hypersurfaceBivector_standardRepresentative ι F Q hF hideal U a b).symm).trans
            (algebraicBivectorBracket_add g U
              (hypersurfaceBivector ι F P hF hideal) (hypersurfaceBivector ι F Q hF hideal) a b).symm))
  map_smul' c P := by
    apply algebraicBivectorBracket_ext_smooth g
    intro U a b
    exact (hypersurfaceBivector_standardRepresentative ι F (c•P) hF hideal U a b).trans
      ((hypersurfaceGlobalBracket_smul_trivector ι F P hF hideal c U a b).trans
        ((congrArg (fun t => AffineSmoothness.coefficientMap g U c * t)
          (hypersurfaceBivector_standardRepresentative ι F P hF hideal U a b).symm).trans
            (algebraicBivectorBracket_coefficient_smul g c
              (show bivectorCoefficientSections g from hypersurfaceBivector ι F P hF hideal) U a b).symm))

@[simp] theorem hypersurfaceBivectorLinear_apply (P : Trivector (n+1)) :
    hypersurfaceBivectorLinear ι F hF hideal P = hypersurfaceBivector ι F P hF hideal := rfl

@[simp] theorem hypersurfaceBivector_zero :
    hypersurfaceBivector ι F 0 hF hideal = 0 :=
  (hypersurfaceBivectorLinear ι F hF hideal).map_zero

@[simp] theorem hypersurfaceBivector_add (P Q : Trivector (n+1)) :
    hypersurfaceBivector ι F (P+Q) hF hideal =
      hypersurfaceBivector ι F P hF hideal + hypersurfaceBivector ι F Q hF hideal :=
  (hypersurfaceBivectorLinear ι F hF hideal).map_add P Q

theorem hypersurfaceBivector_smul (c : ℂ) (P : Trivector (n+1)) :
    hypersurfaceBivector ι F (c•P) hF hideal =
      AffineSmoothness.coefficientMap g ⊤ c • hypersurfaceBivector ι F P hF hideal :=
  (hypersurfaceBivectorLinear ι F hF hideal).map_smul c P

/-- The genuine complex-linear realization is injective in the theorem's
actual smooth cubic range. -/
theorem hypersurfaceBivectorLinear_injective (hN : 5 ≤ n+1) (hF0 : F ≠ 0) :
    Function.Injective (hypersurfaceBivectorLinear ι F hF hideal) := by
  intro P Q h
  have hgrad := ChartComparison.isolated_gradient_of_scheme_smooth ι F hF hF0 hideal
  apply trivector_eq_of_hypersurfaceGlobalBracket_eq ι hN F hF0 hF hgrad hideal P Q
  intro U a b
  exact (hypersurfaceBivector_standardRepresentative ι F P hF hideal U a b).symm.trans
    ((congrArg (fun pi : bivectorCoefficientSections g =>
      (algebraicBivectorBracket g pi).bracket U a b) h).trans
        (hypersurfaceBivector_standardRepresentative ι F Q hF hideal U a b))

end NcCubic.Geometry
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
/-- Surjectivity of the constructed actual complex-linear map is exactly the
remaining geometric representation statement, rather than a dimension assertion. -/
theorem hypersurfaceBivectorLinear_surjective_iff
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    Function.Surjective (hypersurfaceBivectorLinear ι F hF hideal) ↔
      ∀ pi : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n),
        ∃ P : Trivector (n+1), HasStandardRepresentative ι F hF hideal pi P := by
  constructor
  · intro hs pi
    obtain ⟨P,hP⟩ := hs pi
    refine ⟨P,?_⟩
    intro U a b
    exact (congrArg (fun q : bivectorCoefficientSections
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) =>
      (algebraicBivectorBracket _ q).bracket U a b) hP.symm).trans
        (hypersurfaceBivector_standardRepresentative ι F P hF hideal U a b)
  · intro hs pi
    obtain ⟨P,hP⟩ := hs pi
    refine ⟨P,?_⟩
    apply algebraicBivectorBracket_ext_smooth
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
    intro U a b
    exact (hypersurfaceBivector_standardRepresentative ι F P hF hideal U a b).trans (hP U a b).symm
end NcCubic.Geometry
