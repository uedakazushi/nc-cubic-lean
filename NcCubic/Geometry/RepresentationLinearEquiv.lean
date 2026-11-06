/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.PolynomialRepresentation
public import NcCubic.BasisCovariance
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- Actual skew homogeneous quadratic bivectors annihilating the gradient. -/
def horizontalQuadraticBivectors (F : CubicPolynomial N) :
    Submodule ℂ (Fin N → Fin N → CubicPolynomial N) where
  carrier := {q | (∀ i j, q j i = -q i j) ∧
    (∀ i j, (q i j).IsHomogeneous 2) ∧
    (∀ j, ∑ i, q i j * pderiv i F = 0)}
  zero_mem' := by
    refine ⟨by simp, ?_, by simp⟩
    intro i j
    exact (homogeneousSubmodule (Fin N) ℂ 2).zero_mem
  add_mem' := by
    intro q r hq hr
    refine ⟨?_,?_,?_⟩
    · intro i j
      change q j i + r j i = -(q i j + r i j)
      rw [hq.1,hr.1,neg_add]
    · intro i j
      exact (hq.2.1 i j).add (hr.2.1 i j)
    · intro j
      change ∑ i, (q i j + r i j) * pderiv i F = 0
      simp only [add_mul,Finset.sum_add_distrib,hq.2.2,hr.2.2,zero_add]
  smul_mem' := by
    intro c q hq
    refine ⟨?_,?_,?_⟩
    · intro i j
      change c • q j i = -(c • q i j)
      rw [hq.1, smul_neg]
    · intro i j
      change (c • q i j).IsHomogeneous 2
      simpa only [smul_eq_C_mul] using (hq.2.1 i j).C_mul c
    · intro j
      change ∑ i, (c • q i j) * pderiv i F = 0
      simp only [smul_mul_assoc, ← Finset.smul_sum, hq.2.2, smul_zero]

/-- Gradient contraction as a complex-linear map on genuine constant tensors. -/
def gradientContractionLinear (F : CubicPolynomial N) :
    Trivector N →ₗ[ℂ] (Fin N → Fin N → CubicPolynomial N) where
  toFun P := contractionCoefficients F P
  map_add' P Q := by
    funext i j
    simp [contractionCoefficients,trivectorCoefficient,add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' c P := by
    funext i j
    simp only [contractionCoefficients,trivectorCoefficient,smul_apply,smul_eq_mul,
      map_mul,Pi.smul_apply]
    simp [Algebra.smul_def,MvPolynomial.algebraMap_eq,mul_assoc,Finset.mul_sum]

/-- The image of contraction has exactly the required skewness, degree and
horizontality properties. -/
theorem gradientContraction_mem (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (P : Trivector N) : contractionCoefficients F P ∈ horizontalQuadraticBivectors F := by
  refine ⟨contraction_skew F P, ?_, contraction_gradient_zero F P⟩
  intro i j
  unfold contractionCoefficients
  apply IsHomogeneous.sum
  intro a _
  exact (CubicDifferential.derivative_homogeneous hF a).C_mul _

/-- The canonical contraction map with its actual horizontal-quadratic codomain. -/
def horizontalContractionLinear (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) :
    Trivector N →ₗ[ℂ] horizontalQuadraticBivectors F :=
  (gradientContractionLinear F).codRestrict (horizontalQuadraticBivectors F)
    (gradientContraction_mem F hF)
/-- The canonical representation isomorphism is the contraction map itself.
Its surjectivity is the actual graded Koszul theorem, and injectivity follows
from the isolated-gradient hypothesis. -/
def horizontalContractionEquiv (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) :
    Trivector N ≃ₗ[ℂ] horizontalQuadraticBivectors F :=
  LinearEquiv.ofBijective (horizontalContractionLinear F hF) ⟨by
    intro P Q h
    apply contraction_injective hF hgrad
    exact congrArg Subtype.val h, by
    intro q
    obtain ⟨P,hP,_⟩ := horizontal_quadratic_representation F hF hgrad q.val
      q.property.1 q.property.2.1 q.property.2.2
    exact ⟨P,Subtype.ext hP⟩⟩

@[simp] theorem horizontalContractionEquiv_apply_coe
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (P : Trivector N) :
    (horizontalContractionEquiv F hF hgrad P).val = contractionCoefficients F P := rfl

/-- The inverse recovers the unique constant tensor representing the given array. -/
@[simp] theorem horizontalContractionEquiv_symm_contraction
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (q : horizontalQuadraticBivectors F) :
    contractionCoefficients F ((horizontalContractionEquiv F hF hgrad).symm q) = q.val := by
  exact congrArg Subtype.val ((horizontalContractionEquiv F hF hgrad).apply_symm_apply q)

/-- The original exterior cube maps by the genuine contraction representation. -/
def exteriorHorizontalEquiv (F : CubicPolynomial N) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) :
    (⋀[ℂ]^3 (CoordinateSpace N)) ≃ₗ[ℂ] horizontalQuadraticBivectors F :=
  (exteriorTrivectorEquiv N).trans (horizontalContractionEquiv F hF hgrad)

@[simp] theorem exteriorHorizontalEquiv_apply_coe
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (x : ⋀[ℂ]^3 (CoordinateSpace N)) :
    (exteriorHorizontalEquiv F hF hgrad x).val =
      contractionCoefficients F (exteriorTrivectorEquiv N x) := rfl

/-- The canonical representative is compatible with every linear basis
substitution; this is covariance of the actual bracket induced by the map. -/
theorem horizontalContractionEquiv_bracket_covariance {k m : ℕ}
    (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (P : Trivector N) (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (f g : CubicPolynomial N) :
    basisContractionBracket P b (polynomialInBasis F b)
      (polynomialInBasis f b) (polynomialInBasis g b) =
    polynomialInBasis (bracketFromCoefficients
      (horizontalContractionEquiv F hF hgrad P).val f g) b :=
  basisContractionBracket_covariance P b F f g
end NcCubic.Geometry
