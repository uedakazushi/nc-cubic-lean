module
public import NcCubic.Geometry.ImmersionStandardDescent
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry
variable {n : ℕ} {Y : Scheme.{0}}
theorem hasStandardRepresentative_of_bracket_pullback
    (ι : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (P : Trivector (n+1)) (BP : StructureSheafBracket (ProjectiveAmbient n))
    (πY : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (hnat : ∀ U a b, (ι.app U).hom (BP.bracket U a b) =
      (algebraicBivectorBracket
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) πY).bracket
        (ι ⁻¹ᵁ U) ((ι.app U).hom a) ((ι.app U).hom b))
    (heq : ∀ U a b, BP.bracket U a b =
      (ambientProjectiveBracket (contractionCoefficients F P)
        (contractionCoefficients_isHomogeneous F P hF)).bracket U a b) :
    HasStandardRepresentative ι F hF hideal πY P :=
  structureSheafBracket_eq_hypersurfaceGlobalBracket_of_pullback
    ι F hF hideal P BP
    (algebraicBivectorBracket
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) πY) hnat heq
end NcCubic.Geometry
