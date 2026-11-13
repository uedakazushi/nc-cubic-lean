/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.AmbientProjectiveBiderivation
public import NcCubic.Geometry.HypersurfaceGlobalRelative
public import NcCubic.Geometry.GeometricStatement
public import NcCubic.Geometry.ExteriorFunctionalAgreement
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
/-- The actual hypersurface basis carries an alternating biderivation for
EVERY constant trivector; no polynomial Jacobi condition is needed. -/
def hypersurfaceBasisBiderivation
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    BasisBiderivationData Z (subschemeRefinementOpen ι) where
  toBasisBracketData := hypersurfaceBasisBracket ι F P hF hideal
  add_right s := hypersurfaceRefinementBracket_add_right ι F P hF hideal s.1 s.2.2.property
  skew s := hypersurfaceRefinementBracket_skew ι F P hF hideal s.1 s.2.2.property
  self_eq_zero s := hypersurfaceRefinementBracket_self ι F P hF hideal s.1 s.2.2.property
  leibniz s := hypersurfaceRefinementBracket_leibniz ι F P hF hideal s.1 s.2.2.property

def hypersurfaceGlobalBiderivation
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    StructureSheafBiderivation Z :=
  (hypersurfaceBasisBiderivation ι F P hF hideal).glued

@[simp] theorem hypersurfaceGlobalBiderivation_toBracket
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    (hypersurfaceGlobalBiderivation ι F P hF hideal).toStructureSheafBracket =
      hypersurfaceGlobalBracket ι F P hF hideal := rfl

theorem hypersurfaceGlobalBiderivation_relative
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    (hypersurfaceGlobalBiderivation ι F P hF hideal).IsRelative
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) := by
  apply (hypersurfaceBasisBiderivation ι F P hF hideal).glued_relative
  intro s a c
  exact hypersurfaceRefinementBracket_constant_right ι F P hF hideal s.1 s.2.2.property a c
end NcCubic.Geometry
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
/-- Realize EVERY constant trivector by an actual tangent bivector, through a
genuine duality isomorphism. Jacobi and nonzero conditions are not inputs. -/
def hypersurfaceBivectorOfDuality
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (e : bivectorSheaf (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) ≅
      dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)) (2:ℤ))) :
    AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) :=
  biderivationBivectorOfDuality
    (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) e
    (hypersurfaceGlobalBiderivation ι F P hF hideal)
    (hypersurfaceGlobalBiderivation_relative ι F P hF hideal)

theorem hypersurfaceBivectorOfDuality_standardRepresentative
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (e : bivectorSheaf (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) ≅
      dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials
        (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)) (2:ℤ)))
    (he : HasUnitDeterminantFormula
      (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) e.hom) :
    HasStandardRepresentative ι F hF hideal (hypersurfaceBivectorOfDuality ι F P hF hideal e) P := by
  intro U a b
  exact biderivationBivectorOfDuality_bracket
    (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) e he
    (hypersurfaceGlobalBiderivation ι F P hF hideal)
    (hypersurfaceGlobalBiderivation_relative ι F P hF hideal) U a b
end NcCubic.Geometry
