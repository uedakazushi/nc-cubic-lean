/- The coefficient-level representation part of Proposition 2.3.
The actual projective section-to-coefficient comparison remains separate. -/
module
public import NcCubic.Geometry.BivectorCoordinates
public import NcCubic.Geometry.ConstantExterior
public import NcCubic.Geometry.TangentRepresentative
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
open BivectorCoordinates ConstantExterior KoszulCoordinates

/-- Every horizontal quadratic bivector is contraction of a unique genuine
constant trivector. This is the actual graded Koszul representation, with
no exactness or representation hypothesis supplied by the caller. -/
theorem horizontal_quadratic_representation {N : ℕ}
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F)
    (q : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, q j i = -q i j)
    (hdegree : ∀ i j, (q i j).IsHomogeneous 2)
    (hhor : ∀ j, ∑ i, q i j * pderiv i F = 0) :
    ∃! P : Trivector N, contractionCoefficients F P = q := by
  classical
  have hcycle := (bivector_cycle_iff q hskew (fun i => pderiv i F)).2 hhor
  obtain ⟨a, ha⟩ := GradedKoszul.quadratic_bivector_constant_boundary F hF hgrad
    (bivector q) (bivector_homogeneous q hskew hdegree) hcycle
  change Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 2 (polynomialTrivector a) =
    bivector q at ha
  have hP : contractionCoefficients F (constantTrivector a) = q := by
    funext i j
    calc
      _ = coefficient ![i,j]
          (Koszul.d (Koszul.seqDual (fun k => pderiv k F)) 2 (polynomialTrivector a)) :=
        (coefficient_d_polynomialTrivector F a i j).symm
      _ = coefficient ![i,j] (bivector q) := by rw [ha]
      _ = q i j := coefficient_bivector q hskew i j
  refine ⟨constantTrivector a, hP, ?_⟩
  intro Q hQ
  exact contraction_injective hF hgrad (hQ.trans hP.symm)

/-- Corrected projectively tangent quadratic data have a unique constant
trivector representative. The geometric tangency equation is explicit. -/
theorem tangent_quadratic_representation {N : ℕ}
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (hne : F ≠ 0)
    (hgrad : HasIsolatedGradientZero F)
    (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j)
    (hdegree : ∀ i j, (B i j).IsHomogeneous 2)
    (A : Fin N → CubicPolynomial N) (hA : ∀ i, (A i).IsHomogeneous 1)
    (h : CubicPolynomial N)
    (htangent : ∀ j, gradientContract2 F B j = F * A j + h * X j) :
    ∃! P : Trivector N,
      contractionCoefficients F P =
        (fun i j => B i j - (1 / 3 : ℂ) • eulerWedge1 A i j) := by
  apply horizontal_quadratic_representation F hF hgrad
  · exact corrected_tangent_skew B hskew A
  · exact corrected_tangent_homogeneous B hdegree A hA
  · exact corrected_tangent_representative F hF hne B hskew A h htangent
end NcCubic.Geometry
