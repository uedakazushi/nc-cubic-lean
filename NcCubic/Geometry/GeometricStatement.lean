/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
The independently reviewed algebraic geometric target.
This is a proposition definition, not a proof. -/
module
public import NcCubic.Geometry.BivectorSheafDesc
public import NcCubic.Geometry.HypersurfaceStandardComparison
public import NcCubic.Statement
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Jacobi for the actual bracket induced by the actual tangent bivector. -/
def BivectorSatisfiesJacobi {X S : Scheme} (f : X ⟶ S) (π : AlgebraicBivector f) : Prop :=
  ∀ (U : X.Opens) (a b c : Γ(X,U)),
    (algebraicBivectorBracket f π).bracket U a ((algebraicBivectorBracket f π).bracket U b c) +
    (algebraicBivectorBracket f π).bracket U b ((algebraicBivectorBracket f π).bracket U c a) +
    (algebraicBivectorBracket f π).bracket U c ((algebraicBivectorBracket f π).bracket U a b) = 0

/-- The actual every-open bracket of a geometric bivector has the indicated
standard representative. This is an equality to prove, never an input for arbitrary π. -/
def HasStandardRepresentative {n : ℕ} {Z : Scheme}
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (π : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n))
    (P : Trivector (n+1)) : Prop :=
  ∀ (U : Z.Opens) (a b : Γ(Z,U)),
    (algebraicBivectorBracket _ π).bracket U a b =
      (hypersurfaceGlobalBracket ι F P hF hideal).bracket U a b

/-- OPEN algebraic version of the original geometric classification. No
representation, lifting, or comparison result is included as a hypothesis. -/
def GeometricClassificationStatement : Prop :=
  ∀ (n : ℕ), 5 ≤ n+1 → ∀ (Z : Scheme) (ι : Z ⟶ ProjectiveAmbient n)
    [IsClosedImmersion ι] [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (F : CubicPolynomial (n+1)) (_hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}),
    (∀ (π : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)),
      π ≠ 0 → BivectorSatisfiesJacobi _ π →
      ∃ P : Trivector (n+1), HasBlockNormalForm F P ∧ HasStandardRepresentative ι F hF hideal π P) ∧
    (∀ P : Trivector (n+1), HasBlockNormalForm F P →
      ∃ π : AlgebraicBivector (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n),
        π ≠ 0 ∧ BivectorSatisfiesJacobi _ π ∧ HasStandardRepresentative ι F hF hideal π P)
end NcCubic.Geometry
