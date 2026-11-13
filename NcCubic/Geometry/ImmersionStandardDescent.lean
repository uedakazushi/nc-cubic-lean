/- Actual every-open descent of a bivector bracket through the homogeneous affine basis. -/
module
public import NcCubic.Geometry.AmbientQuadraticRatioBracket
public import NcCubic.Geometry.CanonicalImmersionBracket
public import NcCubic.Geometry.GeometricStatement
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry.CotangentCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry
variable {n : ℕ} {Y : Scheme.{0}}

/-- An actual ambient extension represented by a constant trivector descends to
that standard contraction bracket on every open of the hypersurface. -/
theorem structureSheafBracket_eq_hypersurfaceGlobalBracket_of_pullback
    (ι : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (P : Trivector (n+1))
    (BP : StructureSheafBracket (ProjectiveAmbient n)) (BY : StructureSheafBracket Y)
    (hnat : ∀ U a b, (ι.app U).hom (BP.bracket U a b) =
      BY.bracket (ι ⁻¹ᵁ U) ((ι.app U).hom a) ((ι.app U).hom b))
    (heq : ∀ U a b,
      BP.bracket U a b =
      (ambientProjectiveBracket (contractionCoefficients F P)
        (contractionCoefficients_isHomogeneous F P hF)).bracket U a b)
    (U : Y.Opens) (a b : Γ(Y,U)) :
    BY.bracket U a b =
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b := by
  apply (hypersurfaceBasisBracket ι F P hF hideal).glued_unique
  intro s x y
  obtain ⟨x,rfl⟩ := refinementApp_surjective ι s.1 s.2.2.property x
  obtain ⟨y,rfl⟩ := refinementApp_surjective ι s.1 s.2.2.property y
  change BY.bracket
    (ι ⁻¹ᵁ projectiveRefinementOpen s) ((ι.app _).hom x) ((ι.app _).hom y) = _
  rw [← hnat, heq]
  change (ι.app _).hom ((ambientProjectiveBiderivation (contractionCoefficients F P)
    (contractionCoefficients_isHomogeneous F P hF) (contraction_skew F P)).bracket _ x y) = _
  let t : PositiveBasicIndex n := ⟨⟨1+s.2.1, by omega⟩,
    ⟨(X s.1 : CubicPolynomial (n+1)) * (s.2.2 : CubicPolynomial (n+1)), (isHomogeneous_X ℂ s.1).mul s.2.2.property⟩⟩
  have hb := AmbientQuadraticRatioBracket.ambient_biderivation_on_basis
    (contractionCoefficients F P) (contractionCoefficients_isHomogeneous F P hF)
      (contraction_skew F P) t x y
  exact (congrArg (ι.app (projectiveRefinementOpen s)).hom hb).trans
    (hypersurfaceRefinementBracket_pullback ι F P hF hideal s.1 s.2.2.property x y).symm
end NcCubic.Geometry
