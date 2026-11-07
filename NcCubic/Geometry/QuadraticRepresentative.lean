/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ProjectiveQuadraticSections
public import NcCubic.Geometry.PairCoefficients
@[expose] public noncomputable section
namespace NcCubic.Geometry
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
/-- The actual quadratic coefficient array extracted from a global section of
the exterior square of the positive Euler bundle. -/
def quadraticRepresentative (n : ℕ)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2)) :
    Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1) :=
  pairCoefficients
    (fun (s : Set.powersetCard (Fin (n+1)) 2) i => Set.powersetCard.ofFinEmbEquiv.symm s i)
    (fun s => (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n (n+1) σ s).val)

theorem quadraticRepresentative_skew (n : ℕ)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2))
    (i j : Fin (n+1)) : quadraticRepresentative n σ j i = -quadraticRepresentative n σ i j :=
  pairCoefficients_skew _ _ i j

theorem quadraticRepresentative_homogeneous (n : ℕ)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2))
    (i j : Fin (n+1)) : (quadraticRepresentative n σ i j).IsHomogeneous 2 :=
  pairCoefficients_homogeneous _ _ 2
    (fun s => (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n (n+1) σ s).property) i j

/-- Extraction uses precisely the ordered-pair normalization of the canonical
exterior frame, so its polynomial bracket has no spurious factor of two. -/
theorem quadraticRepresentative_bracket (n : ℕ)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2))
    (f g : CubicPolynomial (n+1)) :
    bracketFromCoefficients (quadraticRepresentative n σ) f g =
      ∑ s : Set.powersetCard (Fin (n+1)) 2,
        (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n (n+1) σ s).val *
        (MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s 0) f *
            MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s 1) g -
          MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s 1) f *
            MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s 0) g) :=
  bracketFromPairCoefficients _ _ f g
end NcCubic.Geometry
