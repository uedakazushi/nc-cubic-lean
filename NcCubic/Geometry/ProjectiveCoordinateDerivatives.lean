/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ProjectiveSectionBracket
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.PartialDerivative
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSectionsAreForms
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
namespace NcCubic.Geometry.ProjectiveCoordinateDerivatives
open MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjEulerSequence
variable {n : ℕ}
local instance (x : ProjectiveSpectrum.top (polyGrading ℂ n)) :
    x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime

abbrev coordinateOpen (i : Fin (n+1)) : (ProjectiveAmbient n).Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)

/-- The actual structure-sheaf section X_l/X_i on the standard chart. -/
def coordinateRatio (i l : Fin (n+1)) : Γ(ProjectiveAmbient n, coordinateOpen i) :=
  homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos (Stacks.ProjectiveChart.ratio ℂ i l)

theorem coordinate_mem_primeCompl (i : Fin (n+1)) (x : coordinateOpen i) :
    (X i : CubicPolynomial (n+1)) ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl := x.2

/-- The canonical section has the genuine localized coordinate-ratio value. -/
theorem coordinateRatio_val (i l : Fin (n+1)) (x : coordinateOpen i) :
    HomogeneousLocalization.val ((coordinateRatio i l).1 x) =
      Localization.mk (X l : CubicPolynomial (n+1)) ⟨X i, coordinate_mem_primeCompl i x⟩ := by
  rw [coordinateRatio, homogeneousSectionsEquiv_apply]
  change (HomogeneousLocalization.mapId (homogeneousSubmodule (Fin (n+1)) ℂ)
    (Submonoid.powers_le.mpr x.2) (Stacks.ProjectiveChart.ratio ℂ i l)).val = _
  change Localization.mk ((X l : CubicPolynomial (n+1)) ^ 1)
      ⟨(X i : CubicPolynomial (n+1)) ^ 1,
        by simpa only [pow_one] using coordinate_mem_primeCompl i x⟩ = _
  simp only [pow_one]

/-- The actual projective coordinate derivative is the usual quotient-rule
fraction, at every homogeneous prime of the chart. -/
theorem pderiv_coordinateRatio_val (i l j : Fin (n+1)) (x : coordinateOpen i) :
    (pderivApp ℂ n j (coordinateOpen i) (coordinateRatio i l)).1 x =
      Localization.mk
        ((X i : CubicPolynomial (n+1)) * (if j = l then 1 else 0) -
          X l * (if j = i then 1 else 0))
        ⟨X i * X i, x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
          (coordinate_mem_primeCompl i x) (coordinate_mem_primeCompl i x)⟩ := by
  classical
  simpa [MvPolynomial.pderiv_X, Pi.single_apply, eq_comm] using
    pderivApp_apply_of_val_eq_mk ℂ n j (coordinateOpen i) (coordinateRatio i l) x
      (coordinate_mem_primeCompl i x) (coordinateRatio_val i l x)

/-- The canonical homogeneous degree-section map has value f/1. -/
theorem degreeSectionLinear_val (d : ℕ)
    (f : homogeneousSubmodule (Fin (n+1)) ℂ d)
    (x : (⊤ : Opens (ProjectiveSpectrum.top (polyGrading ℂ n)))) :
    (Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear ℂ n d f).1 x =
      LocalizedModule.mk (f : CubicPolynomial (n+1))
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) := rfl
/-- Actual restriction of the canonical homogeneous-polynomial section. -/
def restrictedDegreeSection (d : ℕ)
    (f : homogeneousSubmodule (Fin (n+1)) ℂ d)
    (U : Opens (ProjectiveSpectrum.top (polyGrading ℂ n))) :=
  (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf (polyGrading ℂ n) (d : ℤ)).val.map
    (homOfLE (show U ≤ ⊤ from le_top)).op
    (Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear ℂ n d f)

/-- Restriction does not alter the actual localized value f/1. -/
theorem restrictedDegreeSection_val (d : ℕ)
    (f : homogeneousSubmodule (Fin (n+1)) ℂ d)
    (U : Opens (ProjectiveSpectrum.top (polyGrading ℂ n))) (x : U) :
    (restrictedDegreeSection d f U).1 x =
      LocalizedModule.mk (f : CubicPolynomial (n+1))
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) := rfl
end NcCubic.Geometry.ProjectiveCoordinateDerivatives
