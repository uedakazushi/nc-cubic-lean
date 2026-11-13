/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.GeometricForward
public import NcCubic.Geometry.GeometricConverse
public import NcCubic.Geometry.SmoothBivectorDuality
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.GeometricForward
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
theorem blockNormalForm_of_standardRepresentative_canonical
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (pi : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (hpi : pi ≠ 0) (hJac : BivectorSatisfiesJacobi _ pi)
    (P : Trivector (n+1)) (hRep : HasStandardRepresentative ι F hF hideal pi P) :
    HasBlockNormalForm F P := by
  exact blockNormalForm_of_standardRepresentative ι hN F hF0 hF hideal
    (smoothBivectorDualityIso (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (smoothBivectorDualityIso_unit (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    pi hpi hJac P hRep
end NcCubic.Geometry.GeometricForward
namespace NcCubic.Geometry.GeometricConverse
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
theorem exists_bivector_of_normalForm
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hNF : HasBlockNormalForm F P) :
    ∃ pi : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n),
      pi ≠ 0 ∧ BivectorSatisfiesJacobi _ pi ∧ HasStandardRepresentative ι F hF hideal pi P := by
  exact exists_bivector_of_normalForm_of_duality ι hN F hF0 P hF hideal
    (smoothBivectorDualityIso (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (smoothBivectorDualityIso_unit (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)) hNF
end NcCubic.Geometry.GeometricConverse
