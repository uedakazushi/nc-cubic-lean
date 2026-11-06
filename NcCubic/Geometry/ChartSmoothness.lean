module
public import NcCubic.Geometry.HypersurfacePresentation
public import NcCubic.Geometry.DehomogenizeNonzero
public import NcCubic.Geometry.JacobianIdeal
public import NcCubic.Geometry.ChartNormalization
public import NcCubic.Geometry.JacobianCondition
public import Mathlib.Algebra.CharZero.Infinite
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.AffineChart
open MvPolynomial
variable {K σ : Type*} [Field K] [Infinite K] [Fintype σ]

omit [Infinite K] [Fintype σ] in
instance pointEvaluation_ker_isPrime
    (F : MvPolynomial (σ ⊕ Unit) K) (x : σ → K)
    (hx : eval x (dehomogenize F) = 0) :
    (RingHom.ker (pointEvaluation F x hx)).IsPrime := RingHom.ker_isPrime _

/-- The actual local-ring smoothness of a standard hypersurface chart at a
rational point is equivalent to nonvanishing of the homogeneous gradient.
This uses Algebra.IsSmoothAt, not a newly defined smoothness predicate. -/
theorem isSmoothAt_point_iff_homogeneous_gradient
    (F : MvPolynomial (σ ⊕ Unit) K) {d : ℕ} (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0) (x : σ → K) (hx : eval x (dehomogenize F) = 0) :
    Algebra.IsSmoothAt K (RingHom.ker (pointEvaluation F x hx)) ↔
      ∃ i : σ ⊕ Unit, eval (lift x) (pderiv i F) ≠ 0 := by
  change Algebra.IsSmoothAt K
    (RingHom.ker (HypersurfacePresentation.pointEvaluation (dehomogenize F) x hx)) ↔ _
  rw [HypersurfacePresentation.isSmoothAt_point_iff (dehomogenize_ne_zero hF hF0)]
  exact exists_nonzero_derivative_iff F hF x hx
/-- The isolated-gradient condition implies actual local-ring smoothness
at every prime of a standard chart, including its nonclosed points. -/
theorem isSmoothAt_of_isolated_gradient [IsAlgClosed K]
    (F : MvPolynomial (σ ⊕ Unit) K) {d : ℕ} (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0)
    (hgrad : ∀ x : σ ⊕ Unit → K, (∀ i, eval x (pderiv i F) = 0) → x = 0)
    (Q : Ideal (CoordinateRing F)) [Q.IsPrime] : Algebra.IsSmoothAt K Q := by
  classical
  by_cases hu : IsUnit (dehomogenize F)
  · have htop : Ideal.span ({dehomogenize F} : Set (MvPolynomial σ K)) = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hu
    let : Subsingleton (CoordinateRing F) := Ideal.Quotient.subsingleton_iff.mpr htop
    have h1 : (1 : CoordinateRing F) ∈ Q := by
      rw [Subsingleton.elim (1 : CoordinateRing F) 0]
      exact Q.zero_mem
    exact False.elim (Ideal.IsPrime.ne_top ‹Q.IsPrime› (Ideal.eq_top_of_isUnit_mem Q h1 isUnit_one))
  · apply (HypersurfacePresentation.isSmoothAt_iff_exists_pderiv_notMem
      (dehomogenize_ne_zero hF hF0) hu Q).2
    obtain ⟨i,hi⟩ := exists_derivative_notMem_prime (dehomogenize F)
      (fun x hx => by
        apply (exists_nonzero_derivative_iff F hF x hx).mpr
        by_contra! hall
        exact lift_ne_zero x (hgrad (lift x) hall)) Q
    exact ⟨i,hi⟩
/-- Isolated homogeneous gradient gives actual smoothness of the entire chart algebra. -/
theorem smooth_of_isolated_gradient [IsAlgClosed K]
    (F : MvPolynomial (σ ⊕ Unit) K) {d : ℕ} (hF : F.IsHomogeneous d)
    (hF0 : F ≠ 0)
    (hgrad : ∀ x : σ ⊕ Unit → K, (∀ i, eval x (pderiv i F) = 0) → x = 0) :
    Algebra.Smooth K (CoordinateRing F) := by
  let : Algebra.FinitePresentation K (CoordinateRing F) :=
    (HypersurfacePresentation.hypersurfacePresentation (dehomogenize F)).finitePresentation_of_isFinite
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp ?_, inferInstance⟩
  apply Set.eq_univ_iff_forall.mpr
  intro Q
  exact isSmoothAt_of_isolated_gradient F hF hF0 hgrad Q.asIdeal

end NcCubic.Geometry.AffineChart

namespace NcCubic.Geometry.ChartComparison
open MvPolynomial
section GeneralField
variable {K : Type*} [Field K] [Infinite K]

omit [Infinite K] in
theorem renamed_gradient_eval {n : ℕ} (F : MvPolynomial (Fin (n+1)) K)
    (j : Fin (n+1)) (y : Fin n → K) (a : Fin (n+1)) :
    eval (AffineChart.lift y) (pderiv (pivotReindex j a) (rename (pivotReindex j) F)) =
      eval (chartLift j y) (pderiv a F) := by
  rw [pderiv_rename (pivotReindex j).injective, eval_rename]
  rfl

omit [Infinite K] in
theorem exists_renamed_gradient_iff {n : ℕ} (F : MvPolynomial (Fin (n+1)) K)
    (j : Fin (n+1)) (y : Fin n → K) :
    (∃ a : Fin n ⊕ Unit, eval (AffineChart.lift y)
      (pderiv a (rename (pivotReindex j) F)) ≠ 0) ↔
    ∃ a : Fin (n+1), eval (chartLift j y) (pderiv a F) ≠ 0 := by
  constructor
  · rintro ⟨a,ha⟩
    have hi := renamed_gradient_eval F j y ((pivotReindex j).symm a)
    rw [(pivotReindex j).apply_symm_apply] at hi
    exact ⟨_, by rwa [← hi]⟩
  · rintro ⟨a,ha⟩
    exact ⟨pivotReindex j a, by rwa [renamed_gradient_eval]⟩

/-- Smoothness at an actual chart rational point detects the original homogeneous gradient. -/
theorem isSmoothAt_pivot_point_iff_gradient {n : ℕ}
    (F : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)
    (j : Fin (n+1)) (y : Fin n → K)
    (hy : eval y (AffineChart.dehomogenize (rename (pivotReindex j) F)) = 0) :
    Algebra.IsSmoothAt K
      (RingHom.ker (AffineChart.pointEvaluation (rename (pivotReindex j) F) y hy)) ↔
      ∃ a : Fin (n+1), eval (chartLift j y) (pderiv a F) ≠ 0 := by
  have hf0 : rename (pivotReindex j) F ≠ 0 := by
    simpa only [ne_eq, rename_eq_zero_iff_of_injective F (pivotReindex j).injective] using hF0
  rw [AffineChart.isSmoothAt_point_iff_homogeneous_gradient _ hF.rename_isHomogeneous hf0]
  exact exists_renamed_gradient_iff F j y

end GeneralField

/-- A cubic's isolated-gradient condition is equivalent to genuine local-ring
smoothness at every rational point of every standard affine chart. -/
theorem isolated_gradient_iff_all_chart_points_smooth {n : ℕ}
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) :
    HasIsolatedGradientZero F ↔
    ∀ (j : Fin (n+1)) (y : Fin n → ℂ)
      (hy : eval y (AffineChart.dehomogenize (rename (pivotReindex j) F)) = 0),
      Algebra.IsSmoothAt ℂ
        (RingHom.ker (AffineChart.pointEvaluation (rename (pivotReindex j) F) y hy)) := by
  classical
  constructor
  · intro hgrad j y hy
    apply (isSmoothAt_pivot_point_iff_gradient F hF hF0 j y hy).2
    by_contra! hall
    have hz := hgrad (chartLift j y) hall
    have hj := congrFun hz j
    simp at hj
  · intro hsmooth x hx
    by_contra hnonzero
    obtain ⟨j,hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra! hh
      exact hnonzero (funext hh)
    let y := normalizedCoordinates j x
    have hxF := cubic_zero_of_gradient_zero F hF x hx
    have hy : eval y (AffineChart.dehomogenize (rename (pivotReindex j) F)) = 0 := by
      rw [AffineChart.eval_dehomogenize, eval_rename]
      change eval (chartLift j y) F = 0
      exact (eval_normalized_zero_iff j x hj F hF).2 hxF
    obtain ⟨a,ha⟩ := (isSmoothAt_pivot_point_iff_gradient F hF hF0 j y hy).1 (hsmooth j y hy)
    exact ha ((gradient_normalized_zero_iff j x hj F hF).2 hx a)

/-- Genuine smoothness of all affine coordinate algebras implies the isolated
homogeneous gradient condition. This is the algebraic input for transporting
scheme smoothness through the coefficient-preserving chart equivalences. -/
theorem isolated_gradient_of_chart_algebras_smooth {n : ℕ}
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (hsmooth : ∀ j : Fin (n+1), Algebra.Smooth ℂ
      (AffineChart.CoordinateRing (rename (pivotReindex j) F))) :
    HasIsolatedGradientZero F := by
  apply (isolated_gradient_iff_all_chart_points_smooth F hF hF0).2
  intro j y hy
  let := hsmooth j
  let : (RingHom.ker (AffineChart.pointEvaluation
      (rename (pivotReindex j) F) y hy)).IsPrime := RingHom.ker_isPrime _
  infer_instance

/-- The isolated-gradient condition is exactly smoothness of every standard chart algebra. -/
theorem isolated_gradient_iff_chart_algebras_smooth {n : ℕ}
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0) :
    HasIsolatedGradientZero F ↔ ∀ j : Fin (n+1), Algebra.Smooth ℂ
      (AffineChart.CoordinateRing (rename (pivotReindex j) F)) := by
  constructor
  · intro hgrad j
    have hf0 : rename (pivotReindex j) F ≠ 0 := by
      simpa only [ne_eq, rename_eq_zero_iff_of_injective F (pivotReindex j).injective] using hF0
    apply AffineChart.smooth_of_isolated_gradient _ hF.rename_isHomogeneous hf0
    intro z hz
    have hzero : z ∘ pivotReindex j = 0 := by
      apply hgrad
      intro a
      have ha := hz (pivotReindex j a)
      rw [pderiv_rename (pivotReindex j).injective, eval_rename] at ha
      exact ha
    funext a
    obtain ⟨b,rfl⟩ := (pivotReindex j).surjective a
    exact congrFun hzero b
  · exact isolated_gradient_of_chart_algebras_smooth F hF hF0

end NcCubic.Geometry.ChartComparison
