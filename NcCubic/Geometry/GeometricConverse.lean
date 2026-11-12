/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.GeometricStatement
public import NcCubic.Geometry.ExteriorFunctionalAgreement
public import NcCubic.Geometry.StandardPoissonConverse
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.GeometricConverse
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
/-- Jacobi transfers along actual every-open bracket equality. -/
theorem jacobi_of_bracket_eq_poisson {X S : Scheme.{u}} (f : X ⟶ S)
    (pi : AlgebraicBivector f) (B : StructureSheafPoisson X)
    (h : ∀ (U : X.Opens) (a b : Γ(X,U)),
      (algebraicBivectorBracket f pi).bracket U a b = B.bracket U a b) :
    BivectorSatisfiesJacobi f pi := by
  intro U a b c
  simpa only [h] using B.jacobi U a b c

/-- A genuine nonzero relative Poisson operation has a genuine bivector
through the specified actual exterior-duality isomorphism. -/
theorem exists_bivector_of_relativePoisson_of_duality {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (e : bivectorSheaf f ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)))
    (he : HasUnitDeterminantFormula f e.hom) (B : StructureSheafPoisson X) (hR : B.IsRelative f)
    (hne : ∃ (U : X.Opens) (a b : Γ(X,U)), B.bracket U a b ≠ 0) :
    ∃ pi : AlgebraicBivector f, pi ≠ 0 ∧ BivectorSatisfiesJacobi f pi ∧
      ∀ (U : X.Opens) (a b : Γ(X,U)), (algebraicBivectorBracket f pi).bracket U a b = B.bracket U a b := by
  let pi := biderivationBivectorOfDuality f e B.toBiderivation hR
  have hpi (U : X.Opens) (a b : Γ(X,U)) :
      (algebraicBivectorBracket f pi).bracket U a b = B.bracket U a b :=
    biderivationBivectorOfDuality_bracket f e he B.toBiderivation hR U a b
  refine ⟨pi, ?_, jacobi_of_bracket_eq_poisson f pi B hpi, hpi⟩
  intro hzero
  obtain ⟨U,a,b,hab⟩ := hne
  apply hab
  exact (hpi U a b).symm.trans
    ((congrArg (fun q => (algebraicBivectorBracket f q).bracket U a b) hzero).trans
      (algebraicBivectorBracket_zero f U a b))
end NcCubic.Geometry.GeometricConverse

namespace NcCubic.Geometry.GeometricConverse
open AlgebraicGeometry CategoryTheory MvPolynomial
open NcCubic.Geometry
open Stacks.AlgebraicGeometry.ReflexiveModules
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
/-- The geometric converse through a genuine exterior-duality isomorphism.
The comparison is visible here and will be instantiated canonically. -/
theorem exists_bivector_of_normalForm_of_duality
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (e : bivectorSheaf (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) ≅
      dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)) (2:ℤ)))
    (he : HasUnitDeterminantFormula
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) e.hom)
    (hNF : HasBlockNormalForm F P) :
    ∃ pi : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n),
      pi ≠ 0 ∧ BivectorSatisfiesJacobi _ pi ∧ HasStandardRepresentative ι F hF hideal pi P := by
  obtain ⟨B,hBrel,hBstd,hBne⟩ :=
    exists_nonzero_standardPoisson_of_normalForm ι hN F hF0 P hF hideal hNF
  obtain ⟨pi,hpi0,hpiJac,hpi⟩ := exists_bivector_of_relativePoisson_of_duality
    (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) e he B hBrel hBne
  exact ⟨pi,hpi0,hpiJac,fun U a b => (hpi U a b).trans (hBstd U a b)⟩
end NcCubic.Geometry.GeometricConverse
