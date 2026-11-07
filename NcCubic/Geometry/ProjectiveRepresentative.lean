/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.EulerLocalization
public import NcCubic.Geometry.AmbientProjectivePoisson
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- Actual homogeneous-basic-open section brackets are independent of the
Euler-wedge representative of the ambient bivector. -/
theorem homogeneousSectionBracket_eq_of_eulerWedge
    (q r : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (hr : ∀ i j, (r i j).IsHomogeneous 2)
    (v : Fin (n+1) → CubicPolynomial (n+1))
    (heq : ∀ i j, r i j = q i j + eulerWedge1 v i j)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a b : Γ(ProjectiveAmbient n, Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    HomogeneousSections.bracket r hr hd hh a b = HomogeneousSections.bracket q hq hd hh a b := by
  exact congrArg (homogeneousSectionsEquiv hh hd)
    (homogeneousBracket_eq_of_eulerWedge q r hq hr v heq hd hh
      ((homogeneousSectionsEquiv hh hd).symm a) ((homogeneousSectionsEquiv hh hd).symm b))

/-- Uniqueness of sheaf gluing transfers Euler representative independence to
every actual open set of projective space. No Jacobi hypothesis is required. -/
theorem ambientProjectiveBracket_eq_of_eulerWedge
    (q r : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (hr : ∀ i j, (r i j).IsHomogeneous 2)
    (v : Fin (n+1) → CubicPolynomial (n+1))
    (heq : ∀ i j, r i j = q i j + eulerWedge1 v i j)
    (U : (ProjectiveAmbient n).Opens) (a b : Γ(ProjectiveAmbient n,U)) :
    (ambientProjectiveBracket r hr).bracket U a b = (ambientProjectiveBracket q hq).bracket U a b := by
  apply (ambientBasisBracket q hq).eq_of_basis
  intro s hs
  exact ((ambientBasisBracket r hr).gluedBracket_restrict U a b s hs).trans
    ((homogeneousSectionBracket_eq_of_eulerWedge q r hq hr v heq s.1.pos s.2.property _ _).trans
      ((ambientBasisBracket q hq).gluedBracket_restrict U a b s hs).symm)
end NcCubic.Geometry
