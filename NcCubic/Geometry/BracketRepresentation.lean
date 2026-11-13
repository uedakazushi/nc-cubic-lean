/- From a genuine homogeneous quadratic ambient bracket preserving a cubic
hypersurface to its constant trivector representative on every open. -/
module
public import NcCubic.Geometry.NormalTangencyExtraction
public import NcCubic.Geometry.ImmersionStandardDescent
public import NcCubic.Geometry.ConstantRepresentativeOfTangency
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry
open NormalTangencyExtraction ProjectiveCoordinateDerivatives
variable {n : ℕ} {Y : Scheme.{0}}

@[simp] theorem StructureSheafBiderivation.zero_left {X : Scheme.{0}}
    (B : StructureSheafBiderivation X) (U : X.Opens) (a : Γ(X,U)) :
    B.bracket U 0 a = 0 := by
  rw [B.skew, B.zero_right, neg_zero]


/-- Genuine pullback compatibility of the two structure-sheaf biderivations
supplies normal tangency and hence a constant trivector representative. -/
theorem exists_standardBracket_of_quadratic_pullback
    (ι : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hd : ∀ i j, (q i j).IsHomogeneous 2) (hs : ∀ i j, q j i = -q i j)
    (BY : StructureSheafBiderivation Y)
    (hnat : ∀ U a b, (ι.app U).hom
        ((ambientProjectiveBiderivation q hd hs).bracket U a b) =
      BY.bracket (ι ⁻¹ᵁ U) ((ι.app U).hom a) ((ι.app U).hom b)) :
    ∃ P : Trivector (n+1), ∀ (U : Y.Opens) (a b : Γ(Y,U)),
      BY.bracket U a b = (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b := by
  have hz : ∀ i j, (ι.app (coordinateOpen i)).hom
      ((ambientProjectiveBiderivation q hd hs).bracket (coordinateOpen i)
        (normalSection F hF i) (coordinateRatio i j)) = 0 := by
    intro i j
    exact (hnat (coordinateOpen i) (normalSection F hF i) (coordinateRatio i j)).trans
      ((congrArg (fun t : Γ(Y, ι ⁻¹ᵁ coordinateOpen i) =>
        BY.bracket (ι ⁻¹ᵁ coordinateOpen i) t
          ((ι.app (coordinateOpen i)).hom (coordinateRatio i j)))
        (normalSection_pullback_zero ι F hF hideal i)).trans
          (BY.zero_left (ι ⁻¹ᵁ coordinateOpen i)
            ((ι.app (coordinateOpen i)).hom (coordinateRatio i j))))
  have hdiv := eulerTangency_divisible_of_normal_pullback_zero
    ι F hF hideal q hd hs hz
  obtain ⟨P,hP⟩ := exists_constantRepresentative_of_tangency F hF0 hF hgrad q hs hd hdiv
  refine ⟨P, ?_⟩
  apply structureSheafBracket_eq_hypersurfaceGlobalBracket_of_pullback
    ι F hF hideal P (ambientProjectiveBiderivation q hd hs).toStructureSheafBracket
      BY.toStructureSheafBracket hnat
  intro U a b
  exact (congrArg (fun D : StructureSheafBracket (ProjectiveAmbient n) => D.bracket U a b)
    (ambientProjectiveBiderivation_toBracket q hd hs)).trans (hP U a b).symm
end NcCubic.Geometry
