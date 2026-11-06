module
public import NcCubic.CubicDifferential
@[expose] public section
noncomputable section
namespace NcCubic.GradientIndependence
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- Constant gradient syzygies vanish using the cubic Euler identity alone.
No regular-sequence or geometric comparison is assumed. -/
theorem constant_syzygy_zero {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (c : CoordinateSpace N)
    (hc : ∑ i, C (c i) * pderiv i F = 0) : c = 0 := by
  apply hgrad c
  intro j
  have hder := congrArg (pderiv j) hc
  simp at hder
  have heval := congrArg (eval c) hder
  simp only [map_sum, map_mul, eval_C, map_zero] at heval
  have heuler := congrArg (eval c)
    (CubicDifferential.derivative_homogeneous hF j).sum_X_mul_pderiv
  simp [map_sum, map_mul, nsmul_eq_mul] at heuler
  have heq : 2 * eval c (pderiv j F) = 0 := by
    rw [← heuler]
    simpa only [pderiv_comm j] using heval
  exact (mul_eq_zero.mp heq).resolve_left (by norm_num)

theorem gradient_linearlyIndependent {F : CubicPolynomial N} (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) :
    LinearIndependent ℂ (fun i : Fin N => pderiv i F) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz := constant_syzygy_zero hF hgrad c (by simpa [smul_eq_C_mul] using hc)
  exact congrFun hz i
end NcCubic.GradientIndependence
