/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.AmbientQuadraticRatioBracket
public import NcCubic.Geometry.ProjectiveHypersurfaceSections
public import NcCubic.Geometry.NormalTangencyDivisibility
public import NcCubic.Geometry.ProjectiveCoordinateDerivatives
public import NcCubic.Geometry.CanonicalImmersionBracket
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry.CotangentCoordinates
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry.NormalTangencyExtraction
open ProjectiveCoordinateDerivatives
variable {n : ℕ} {Y : Scheme.{0}}

/-- The genuine normalized defining equation F/X_i³ on the standard chart. -/
def normalSection (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3) (i : Fin (n+1)) :
    Γ(ProjectiveAmbient n, coordinateOpen i) :=
  homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos (projectiveEquation F hF i)

/-- The actual chart presentation detects the kernel of the closed-immersion
map on degree-zero fractions. No bracket or smoothness assumption is needed. -/
theorem mem_equation_ideal_of_pullback_zero
    (ι : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (i : Fin (n+1)) (a : ProjectiveChartRing i)
    (ha : (ι.app (coordinateOpen i)).hom
      (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos a) = 0) :
    a ∈ Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i)) := by
  let E := projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply E.injective
  rw [map_zero]
  exact (projectiveHypersurfaceChartSectionsEquiv_mk ι F hF hideal i a).trans ha

/-- The genuine normal equation pulls back to zero on the actual hypersurface. -/
theorem normalSection_pullback_zero
    (ι : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1)) :
    (ι.app (coordinateOpen i)).hom (normalSection F hF i) = 0 := by
  have he : Ideal.Quotient.mk
      (Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i)))
      (projectiveEquation F hF i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have h := congrArg (projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i) he
  rw [projectiveHypersurfaceChartSectionsEquiv_mk, map_zero] at h
  exact h

/-- Vanishing of the actual normal-coordinate brackets forces the polynomial
Euler tangency divisibilities. -/
theorem eulerTangency_divisible_of_normal_pullback_zero
    (ι : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (hs : ∀ i j, q j i = -q i j)
    (hz : ∀ i j, (ι.app (coordinateOpen i)).hom
      ((ambientProjectiveBiderivation q hq hs).bracket (coordinateOpen i)
        (normalSection F hF i) (coordinateRatio i j)) = 0) :
    ∀ i j, F ∣ eulerWedge1 (gradientContract2 F q) i j := by
  apply eulerTangency_divisible_of_normal_brackets q hs F
  intro i j
  have hh := hz i j
  rw [normalSection, coordinateRatio,
    AmbientQuadraticRatioBracket.ambient_biderivation_chart_equiv] at hh
  have hm := mem_equation_ideal_of_pullback_zero ι F hF hideal i _ hh
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hm
  rw [← normalFraction_ideal_eq F i]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨a.val, ?_⟩
  have hv := congrArg HomogeneousLocalization.val ha
  rw [HomogeneousLocalization.val_mul, HomogeneousBasic.bracket_val,
    ← normalFraction_eq_projectiveEquation_val, projectiveRatio_val] at hv
  exact hv
end NcCubic.Geometry.NormalTangencyExtraction
