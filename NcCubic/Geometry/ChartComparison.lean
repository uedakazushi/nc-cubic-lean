/- Genuine projective hypersurface charts, their coefficient algebra structures,
and comparison of scheme smoothness with the homogeneous cubic gradient.
The six-line chart-cover proof is adapted from pinned Stacks
ProjectiveChart.HypersurfaceFinitePresentation (Tag 01NG). -/
module
public import NcCubic.Geometry.ChartNormalization
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceChart
public import NcCubic.Geometry.AffineSmoothness
public import NcCubic.Geometry.ChartSmoothness
public import NcCubic.Geometry.AffineSmoothnessCover
@[expose] public section
noncomputable section
open MvPolynomial
namespace NcCubic.Geometry.ChartComparison
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R : Type u} [CommRing R]

/-- The pinned geometric chart substitution agrees with the concrete sum-indexed one. -/
theorem dehomCoeff_eq_dehomogenize {n : ℕ} (j : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) :
    Stacks.ProjectiveChart.dehomCoeff R j F =
      AffineChart.dehomogenize (rename (pivotReindex j) F) := by
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
  exact substitution_eq j F

theorem eval_dehomCoeff {n : ℕ} (j : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) (x : Fin n → R) :
    eval x (Stacks.ProjectiveChart.dehomCoeff R j F) = eval (chartLift j x) F := by
  rw [dehomCoeff_eq_dehomogenize, AffineChart.eval_dehomogenize, eval_rename]
  rfl

theorem pderiv_dehomCoeff {n : ℕ} (j : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) (a : Fin n) :
    pderiv a (Stacks.ProjectiveChart.dehomCoeff R j F) =
      Stacks.ProjectiveChart.dehomCoeff R j (pderiv (j.succAbove a) F) := by
  rw [dehomCoeff_eq_dehomogenize, AffineChart.pderiv_dehomogenize]
  have h := pderiv_rename (pivotReindex j).injective (j.succAbove a) F
  rw [pivotReindex_succAbove] at h
  rw [h, ← dehomCoeff_eq_dehomogenize]

theorem reindexed_gradient_zero_iff {n : ℕ} (j : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) (x : Fin n → R) :
    (∀ a : Fin n ⊕ Unit, eval (AffineChart.lift x) (pderiv a (rename (pivotReindex j) F)) = 0) ↔
      ∀ k : Fin (n+1), eval (chartLift j x) (pderiv k F) = 0 := by
  constructor
  · intro h k
    have hk := h (pivotReindex j k)
    rw [pderiv_rename (pivotReindex j).injective, eval_rename] at hk
    exact hk
  · intro h a
    obtain ⟨k,rfl⟩ := (pivotReindex j).surjective a
    rw [pderiv_rename (pivotReindex j).injective, eval_rename]
    exact h k

theorem chart_gradient_zero_iff {n : ℕ} (j : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) R) {d : ℕ} (hF : F.IsHomogeneous d)
    (x : Fin n → R) (hx : eval x (Stacks.ProjectiveChart.dehomCoeff R j F) = 0) :
    (∀ a : Fin n, eval x (pderiv a (Stacks.ProjectiveChart.dehomCoeff R j F)) = 0) ↔
      ∀ k : Fin (n+1), eval (chartLift j x) (pderiv k F) = 0 := by
  have hr : (rename (pivotReindex j) F).IsHomogeneous d :=
    (IsHomogeneous.rename_isHomogeneous_iff (pivotReindex j).injective).mpr hF
  rw [dehomCoeff_eq_dehomogenize] at hx ⊢
  exact (AffineChart.gradient_zero_iff_on_hypersurface _ hr x hx).trans
    (reindexed_gradient_zero_iff j F x)

/-- At any nonzero pivot, the genuine chart Jacobian at the normalized point
vanishes exactly when the original homogeneous gradient vanishes. -/
theorem normalized_chart_gradient_zero_iff {K : Type u} [Field K] {n : ℕ} (j : Fin (n+1))
    (F : MvPolynomial (Fin (n+1)) K) {d : ℕ} (hF : F.IsHomogeneous d)
    (x : Fin (n+1) → K) (hj : x j ≠ 0) (hx : eval x F = 0) :
    (∀ a : Fin n, eval (normalizedCoordinates j x)
      (pderiv a (Stacks.ProjectiveChart.dehomCoeff K j F)) = 0) ↔
      ∀ k : Fin (n+1), eval x (pderiv k F) = 0 := by
  have hzero : eval (normalizedCoordinates j x) (Stacks.ProjectiveChart.dehomCoeff K j F) = 0 := by
    rw [eval_dehomCoeff]
    exact (eval_normalized_zero_iff j x hj F hF).mpr hx
  exact (chart_gradient_zero_iff j F hF _ hzero).trans
    (gradient_normalized_zero_iff j x hj F hF)

/-- The actual scheme chart has precisely our concrete polynomial quotient ring. -/
def chartCoordinateRingSectionsEquiv {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) [IsClosedImmersion i] [IsNoetherianRing R]
    (F : MvPolynomial (Fin (n+1)) R) {d : ℕ}
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n+1)) R (d • 1))
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R) i = Ideal.span {F}) :
    AffineChart.CoordinateRing (rename (pivotReindex j) F) ≃+*
      Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
  (Ideal.quotEquivOfEq (congrArg (fun p : MvPolynomial (Fin n) R => Ideal.span ({p} : Set _))
    (dehomCoeff_eq_dehomogenize j F).symm)).trans
      (Stacks.ProjectiveChart.chartQuotientEquiv i j F hF hideal)


/-- The equivalence is the canonical restriction map on quotient polynomial functions. -/
theorem chartCoordinateRingSectionsEquiv_mk {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) [IsClosedImmersion i] [IsNoetherianRing R]
    (F : MvPolynomial (Fin (n+1)) R) {d : ℕ}
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n+1)) R (d • 1))
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R) i = Ideal.span {F}) (p : MvPolynomial (Fin n) R) :
    chartCoordinateRingSectionsEquiv i j F hF hideal (Ideal.Quotient.mk _ p) =
      Stacks.ProjectiveChart.chartPresentation i j p := by
  rfl

/-- Coefficients act by pullback along the actual hypersurface structure morphism. -/
def chartCoefficientMap {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) : R →+* Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
  AffineSmoothness.coefficientMap
    (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n)
    (Stacks.ProjectiveChart.subschemeChart i j)

/-- The canonical coefficient pullback is the restriction presentation on constants. -/
theorem chartCoefficientMap_eq_chartPresentation_comp_C {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) :
    chartCoefficientMap i j = (Stacks.ProjectiveChart.chartPresentation i j).comp C := by
  ext r
  exact (Stacks.ProjectiveChart.chartPresentation_C i j r).symm

/-- The section-ring equivalence also respects the coefficient algebra structure. -/
def chartCoordinateRingSectionsAlgEquiv {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) [IsClosedImmersion i] [IsNoetherianRing R]
    (F : MvPolynomial (Fin (n+1)) R) {d : ℕ}
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n+1)) R (d • 1))
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R) i = Ideal.span {F}) :
    letI : Algebra R Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
      (chartCoefficientMap i j).toAlgebra
    AffineChart.CoordinateRing (rename (pivotReindex j) F) ≃ₐ[R]
      Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) := by
  letI : Algebra R Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
    (chartCoefficientMap i j).toAlgebra
  refine { chartCoordinateRingSectionsEquiv i j F hF hideal with commutes' := ?_ }
  intro r
  change chartCoordinateRingSectionsEquiv i j F hF hideal
    (Ideal.Quotient.mk _ (C r)) = chartCoefficientMap i j r
  rw [chartCoordinateRingSectionsEquiv_mk]
  exact Stacks.ProjectiveChart.chartPresentation_C i j r


/-- Genuine scheme smoothness supplies smoothness of the actual chart coefficient map. -/
theorem chartCoefficientMap_smooth {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) [IsClosedImmersion i]
    [Smooth (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n)] :
    (chartCoefficientMap i j).Smooth := by
  exact AffineSmoothness.coefficientMap_smooth
    (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n) _
    (Stacks.ProjectiveChart.isAffineOpen_subschemeChart i j)

/-- Smoothness of the actual hypersurface over R transfers to its explicit chart quotient. -/
theorem chartCoordinateRing_smooth {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) [IsClosedImmersion i] [IsNoetherianRing R]
    (F : MvPolynomial (Fin (n+1)) R) {d : ℕ}
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n+1)) R (d • 1))
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R) i = Ideal.span {F})
    [Smooth (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n)] :
    Algebra.Smooth R (AffineChart.CoordinateRing (rename (pivotReindex j) F)) := by
  let : Algebra R Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
    (chartCoefficientMap i j).toAlgebra
  let : Algebra.Smooth R Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
    (chartCoefficientMap_smooth i j).toAlgebra
  exact Algebra.Smooth.of_equiv (chartCoordinateRingSectionsAlgEquiv i j F hF hideal).symm

/-- Smoothness of a genuine projective cubic hypersurface implies that its
homogeneous gradient vanishes only at the origin. -/
theorem isolated_gradient_of_scheme_smooth {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    [IsClosedImmersion i]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F})
    [Smooth (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)] :
    HasIsolatedGradientZero F := by
  apply isolated_gradient_of_chart_algebras_smooth F hF hF0
  intro j
  apply chartCoordinateRing_smooth i j F (d := 3) _ hideal
  simpa using hF

/-- The actual coefficient map is smooth if the explicit chart quotient is smooth. -/
theorem chartCoefficientMap_smooth_of_coordinateRing {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R))
    (j : Fin (n+1)) [IsClosedImmersion i] [IsNoetherianRing R]
    (F : MvPolynomial (Fin (n+1)) R) {d : ℕ}
    (hF : F ∈ MvPolynomial.homogeneousSubmodule (Fin (n+1)) R (d • 1))
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R) i = Ideal.span {F})
    [Algebra.Smooth R (AffineChart.CoordinateRing (rename (pivotReindex j) F))] :
    (chartCoefficientMap i j).Smooth := by
  let : Algebra R Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
    (chartCoefficientMap i j).toAlgebra
  let : Algebra.Smooth R Γ(Z, Stacks.ProjectiveChart.subschemeChart i j) :=
    Algebra.Smooth.of_equiv (chartCoordinateRingSectionsAlgEquiv i j F hF hideal)
  exact (RingHom.smooth_algebraMap).2 inferInstance

/-- The standard affine chart opens cover the actual closed subscheme.
Proof adapted from pinned Stacks ProjectiveChart.HypersurfaceFinitePresentation. -/
theorem iSup_subschemeChart_eq_top {n : ℕ} {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R)) :
    ⨆ j : Fin (n+1), Stacks.ProjectiveChart.subschemeChart i j = ⊤ := by
  have h := TopologicalSpace.Opens.map_iSup i.base
    (fun l : Fin (n+1) => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n+1)) R)
      (MvPolynomial.X l))
  rw [Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top R n] at h
  exact h.symm.trans rfl

/-- For a genuine projective cubic hypersurface, scheme smoothness is exactly
nonvanishing of the homogeneous gradient away from the origin. -/
theorem scheme_smooth_iff_isolated_gradient {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ))
    [IsClosedImmersion i]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F}) :
    Smooth (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) ↔
      HasIsolatedGradientZero F := by
  constructor
  · intro h
    let := h
    exact isolated_gradient_of_scheme_smooth i F hF hF0 hideal
  · intro hgrad
    apply AffineSmoothness.smooth_of_coefficientMaps
      (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
      (fun j => ⟨Stacks.ProjectiveChart.subschemeChart i j,
        Stacks.ProjectiveChart.isAffineOpen_subschemeChart i j⟩)
      (iSup_subschemeChart_eq_top i)
    intro j
    let := (isolated_gradient_iff_chart_algebras_smooth F hF hF0).1 hgrad j
    exact chartCoefficientMap_smooth_of_coordinateRing i j F (d := 3)
      (by simpa using hF) hideal

end NcCubic.Geometry.ChartComparison
