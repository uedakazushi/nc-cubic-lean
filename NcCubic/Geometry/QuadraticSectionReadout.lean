/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.QuadraticEulerLift
public import NcCubic.Geometry.QuadraticRepresentative
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NcCubic.Geometry.QuadraticEulerLift
open Stacks.AlgebraicGeometry.ProjTwistRank

/-- Restricting coefficient scalars does not change the actual section type.
This is the identity on the genuine positive-Euler bivector section. -/
def coefficientSectionEquiv (n : ℕ) :
    Γ(positiveBivectorBundle n, ⊤) ≃
      (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2) :=
  Equiv.refl _

/-- Actual quadratic coefficients of a native positive-Euler section. -/
def nativeQuadraticRepresentative (n : ℕ) (σ : Γ(positiveBivectorBundle n, ⊤)) :
    Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1) :=
  quadraticRepresentative n (coefficientSectionEquiv n σ)

theorem nativeQuadraticRepresentative_skew (n : ℕ)
    (σ : Γ(positiveBivectorBundle n, ⊤)) (i j : Fin (n+1)) :
    nativeQuadraticRepresentative n σ j i = -nativeQuadraticRepresentative n σ i j :=
  quadraticRepresentative_skew n (coefficientSectionEquiv n σ) i j

theorem nativeQuadraticRepresentative_homogeneous (n : ℕ)
    (σ : Γ(positiveBivectorBundle n, ⊤)) (i j : Fin (n+1)) :
    (nativeQuadraticRepresentative n σ i j).IsHomogeneous 2 :=
  quadraticRepresentative_homogeneous n (coefficientSectionEquiv n σ) i j
end NcCubic.Geometry.QuadraticEulerLift
