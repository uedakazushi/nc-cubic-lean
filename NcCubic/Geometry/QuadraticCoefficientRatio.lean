module
public import NcCubic.Geometry.CoordinateTwistFrame
public import NcCubic.Geometry.ProjectiveCoordinateDerivatives
@[expose] public noncomputable section
namespace NcCubic.Geometry.QuadraticCoefficientRatio
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ProjTrivialization
open ProjectiveCoordinateDerivatives CoordinateTwistFrame
attribute [local instance] MvPolynomial.gradedAlgebra ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}
local instance (x : ProjectiveSpectrum.top (polyGrading ℂ n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime

/-- The genuine homogeneous degree-zero quadratic fraction on the standard chart. -/
def quadraticChartFraction (c : homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) : ProjectiveChartRing i :=
  HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin (n+1)) ℂ)
    (isHomogeneous_X ℂ i) 2 c c.2

/-- The quadratic coefficient c/X_i² on every subopen of the standard chart. -/
def ratioQuadratic (c : homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) :
    Γ(ProjectiveAmbient n,U) :=
  (ProjectiveAmbient n).presheaf.map (homOfLE hU).op
    (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos (quadraticChartFraction c i))

/-- Its pointwise value is the literal localized fraction. -/
theorem ratioQuadratic_val (c : homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) (x : U) :
    HomogeneousLocalization.val ((ratioQuadratic c i U hU).1 x) =
      Localization.mk (c : CubicPolynomial (n+1))
        (⟨X i,hU x.2⟩ ^ 2 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
  change HomogeneousLocalization.val
    ((homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos
      (quadraticChartFraction c i)).1 ⟨x.1,hU x.2⟩) = _
  rw [homogeneousSectionsEquiv_apply]
  rfl

/-- A homogeneous quadratic section is its actual chart coefficient times the
canonical quadratic frame. -/
theorem ratioQuadratic_smul_frameTwo (c : homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) :
    ratioQuadratic c i U hU • frameTwo i U hU = restrictedDegreeSection 2 c U := by
  apply Subtype.ext
  funext x
  rw [smul_sections_apply, ratioQuadratic_val, frameTwo_val, restrictedDegreeSection_val]
  change Localization.mk (c : CubicPolynomial (n+1))
      (⟨X i,hU x.2⟩ ^ 2 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) *
    algebraMap (CubicPolynomial (n+1)) (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
      (↑(⟨X i,hU x.2⟩ ^ 2 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)) =
    algebraMap (CubicPolynomial (n+1)) (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) c
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ _ _

/-- Every scalar expression in the canonical quadratic frame has the genuine
fraction coefficient, rather than an unidentified choice of trivialization. -/
theorem coefficient_eq_ratioQuadratic (c : homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i : Fin (n+1)) (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i)
    (r : Γ(ProjectiveAmbient n,U))
    (hr : r • frameTwo i U hU = restrictedDegreeSection 2 c U) :
    r = ratioQuadratic c i U hU := by
  obtain ⟨r₀,_,huniq⟩ := existsUnique_smul_powSection (polyGrading ℂ n)
    (isHomogeneous_X ℂ i) 2 hU (restrictedDegreeSection 2 c U)
  exact (huniq r hr).trans (huniq _ (ratioQuadratic_smul_frameTwo c i U hU)).symm
end NcCubic.Geometry.QuadraticCoefficientRatio
