module
public import NcCubic.Geometry.CoordinateTwistFrame
public import NcCubic.Geometry.CanonicalTwistEvaluation
@[expose] public noncomputable section
namespace NcCubic.Geometry.CanonicalEulerCoordinateEvaluation
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
open ProjectiveCoordinateDerivatives CoordinateTwistFrame
attribute [local instance] MvPolynomial.gradedAlgebra ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Cancel the coordinate frame against the denominator in the quotient rule. -/
theorem localization_quotient_frame {R : Type*} [CommRing R] (M : Submonoid R)
    (t : M) (a u v : R) :
    algebraMap R (Localization M) (t:R) *
      Localization.mk ((t:R)*u-a*v) (t*t) =
      algebraMap R (Localization M) u -
        Localization.mk a t * algebraMap R (Localization M) v := by
  rw [Localization.mk_eq_mk', IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply (IsLocalization.mk'_eq_iff_eq_mul).2
  have hk := IsLocalization.mk'_spec (Localization M) a t
  simp only [map_mul, map_sub, Submonoid.coe_mul] at *
  linear_combination (algebraMap R (Localization M) (t:R) *
    algebraMap R (Localization M) v) * hk

variable {n : ℕ}
local instance (x : ProjectiveSpectrum.top (polyGrading ℂ n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime

/-- A coordinate ratio restricted to an arbitrary subopen of its standard chart. -/
def restrictedRatio (i l : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ coordinateOpen i) : Γ(ProjectiveAmbient n,U) :=
  (ProjectiveAmbient n).presheaf.map (homOfLE hU).op (coordinateRatio i l)

/-- Restriction leaves the quotient-rule value unchanged. -/
theorem pderiv_restrictedRatio_val (i l j : Fin (n+1))
    (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) (x : U) :
    (pderivApp ℂ n j U (restrictedRatio i l U hU)).1 x =
      Localization.mk
        ((X i : CubicPolynomial (n+1)) * (if j=l then 1 else 0) -
          X l * (if j=i then 1 else 0))
        ⟨X i * X i, x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
          (hU x.2) (hU x.2)⟩ := by
  exact pderiv_coordinateRatio_val i l j ⟨x.1,hU x.2⟩

/-- The positive coordinate frame cancels one quotient-rule denominator. -/
theorem canonicalEulerField_frame_ratio_val (i l j : Fin (n+1))
    (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) (x : U) :
    HomogeneousLocalization.val
      ((tangentSectionDerivation (projToSpecCoeff ℂ n) U
        (Scheme.Modules.Hom.app (canonicalEulerField ℂ n j) U (frameOne i U hU))
        (restrictedRatio i l U hU)).1 x) =
      algebraMap (CubicPolynomial (n+1)) (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (if j=l then 1 else 0) -
      Localization.mk (X l : CubicPolynomial (n+1)) ⟨X i,hU x.2⟩ *
        algebraMap (CubicPolynomial (n+1)) (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (if j=i then 1 else 0) := by
  rw [canonicalEulerField_action]
  rw [CanonicalTwistDuality.twistPairing_tmul_val, frameOne_val,
    pderiv_restrictedRatio_val]
  exact localization_quotient_frame x.1.asHomogeneousIdeal.toIdeal.primeCompl
    ⟨X i,hU x.2⟩ (X l) (if j=l then 1 else 0) (if j=i then 1 else 0)
/-- The canonical coordinate Euler field is the genuine chart quotient-rule
vector field on every subopen of the standard chart. -/
theorem canonicalEulerField_frame_ratio (i l j : Fin (n+1))
    (U : (ProjectiveAmbient n).Opens) (hU : U ≤ coordinateOpen i) :
    tangentSectionDerivation (projToSpecCoeff ℂ n) U
      (Scheme.Modules.Hom.app (canonicalEulerField ℂ n j) U (frameOne i U hU))
      (restrictedRatio i l U hU) =
      (if j=l then 1 else 0) - restrictedRatio i l U hU * (if j=i then 1 else 0) := by
  classical
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [canonicalEulerField_frame_ratio_val]
  have hr : HomogeneousLocalization.val ((restrictedRatio i l U hU).1 x) =
      Localization.mk (X l : CubicPolynomial (n+1)) ⟨X i,hU x.2⟩ :=
    coordinateRatio_val i l ⟨x.1,hU x.2⟩
  split_ifs
  · change _ = HomogeneousLocalization.val (1 - (restrictedRatio i l U hU).1 x * 1)
    simp only [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, map_one, hr]
  · change _ = HomogeneousLocalization.val (1 - (restrictedRatio i l U hU).1 x * 0)
    simp only [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, HomogeneousLocalization.val_zero, map_one, map_zero, hr]
  · change _ = HomogeneousLocalization.val (0 - (restrictedRatio i l U hU).1 x * 1)
    simp only [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_one, HomogeneousLocalization.val_zero, map_one, map_zero, hr]
  · change _ = HomogeneousLocalization.val (0 - (restrictedRatio i l U hU).1 x * 0)
    simp only [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_zero, map_zero, hr]

end NcCubic.Geometry.CanonicalEulerCoordinateEvaluation
