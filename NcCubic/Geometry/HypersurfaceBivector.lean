/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.HypersurfaceBiderivation
public import NcCubic.Geometry.SmoothBivectorDuality
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
/-- Every constant trivector defines a genuine global tangent bivector on the
actual smooth cubic. No Jacobi, normal form or comparison data is an input. -/
def hypersurfaceBivector
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) :=
  hypersurfaceBivectorOfDuality ι F P hF hideal
    (smoothBivectorDualityIso (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))

/-- The canonical genuine bivector induces the standard contraction operation
on EVERY actual open, for every constant trivector. -/
theorem hypersurfaceBivector_standardRepresentative
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    HasStandardRepresentative ι F hF hideal (hypersurfaceBivector ι F P hF hideal) P :=
  hypersurfaceBivectorOfDuality_standardRepresentative ι F P hF hideal
    (smoothBivectorDualityIso (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (smoothBivectorDualityIso_unit (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
end NcCubic.Geometry
