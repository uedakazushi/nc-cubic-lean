/- Paper Lemma 3.1: the unconditional Hessian criterion for a smooth cubic. -/
module
public import NcCubic.HessianCompatibility
public import NcCubic.GradientRegularity

@[expose] public section
noncomputable section
namespace NcCubic.CubicJacobi
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- On a cubic with isolated gradient zero, the full polynomial Jacobi identity
is exactly the covector-level Hessian compatibility condition. This theorem
uses the proved CM/Koszul syzygy result, not a regularity assumption. -/
theorem jacobi_iff_hessians_compatible (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) ↔
      ∀ p, HessianCompatibility.Compatible P (CubicDifferential.hessianForm F p) := by
  apply HessianCompatibility.jacobi_iff_all_hessians_compatible_of_no_linear_syzygy F P hF
  intro A hA hz a
  have hzero := GradientRegularity.cubic_linear_syzygy_zero F hF hgrad A
    (fun i => (hA i).totalDegree_le) (by simpa only [mul_comm] using hz)
  exact congrFun hzero a

/-- The symmetric compatibility space K(P) of a Poisson cubic is basepoint-free. -/
theorem compatibleForms_basepoint_free_of_jacobi (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (hJ : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)))
    (w : CoordinateSpace N) (hw : w ≠ 0) :
    ∃ H ∈ HessianCompatibility.compatibleForms P, H w w ≠ 0 :=
  HessianCompatibility.compatibleForms_basepoint_free F P hF hgrad
    ((jacobi_iff_hessians_compatible F P hF hgrad).1 hJ) w hw

end NcCubic.CubicJacobi
