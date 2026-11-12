/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.GeometricStatement
public import NcCubic.Geometry.StandardBracketClassification
public import NcCubic.Geometry.BivectorFaithfulness
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.GeometricForward
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry
open Stacks.AlgebraicGeometry.ReflexiveModules
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
/-- A given actual standard representative of a nonzero Poisson bivector has
block normal form. Existence of the representative is a separate theorem. -/
theorem blockNormalForm_of_standardRepresentative
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (e : bivectorSheaf (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) ≅
      dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)) (2:ℤ)))
    (he : HasUnitDeterminantFormula
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) e.hom)
    (pi : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (hpi : pi ≠ 0) (hJac : BivectorSatisfiesJacobi _ pi)
    (P : Trivector (n+1)) (hRep : HasStandardRepresentative ι F hF hideal pi P) :
    HasBlockNormalForm F P := by
  have hrepr (U : Z.Opens) (a b : Γ(Z,U)) :
      (algebraicBivectorBracket
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) pi).bracket U a b =
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b := hRep U a b
  have hP : P ≠ 0 := by
    intro hzero
    subst P
    apply hpi
    apply algebraicBivector_eq_zero_of_bracket_zero_of_duality _ e he pi
    intro U a b
    exact (hrepr U a b).trans (hypersurfaceGlobalBracket_zero_trivector ι F hF hideal U a b)
  apply (standardBracketJacobi_iff_blockNormalForm ι hN F hF0 P hP hF hideal).1
  intro U a b c
  simpa only [hrepr] using hJac U a b c
end NcCubic.Geometry.GeometricForward
