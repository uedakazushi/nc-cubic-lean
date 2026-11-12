/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.PairCoefficients
public import NcCubic.Geometry.LocalChartHamiltonian
public import NcCubic.Geometry.LocalizedBracket
set_option autoImplicit false
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
section Map
variable {ι κ A B : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [CommRing A] [CommRing B]
omit [Fintype ι] in
theorem pairCoefficients_map (f : A →+* B) (idx : κ → Fin 2 → ι) (c : κ → A) (i j : ι) :
    f (pairCoefficients idx c i j) = pairCoefficients idx (fun s => f (c s)) i j := by
  classical
  simp only [pairCoefficients, map_sum, map_sub, apply_ite, map_zero]
end Map

section Localized
variable {N : ℕ} {κ : Type*} [Fintype κ]
variable (S : Submonoid (CubicPolynomial N)) (L : Type*) [CommRing L]
  [Algebra (CubicPolynomial N) L] [IsLocalization S L] [Algebra ℂ L]
  [IsScalarTower ℂ (CubicPolynomial N) L]

/-- Ordered-pair coefficients evaluate on arbitrary localized functions with
exactly the determinant normalization, without an extra factor of two. -/
theorem localized_bracket_pairCoefficients (idx : κ → Fin 2 → Fin N)
    (c : κ → CubicPolynomial N) (a b : L) :
    LocalizedPoisson.bracket S L (pairCoefficients idx c) a b =
      ∑ s, algebraMap (CubicPolynomial N) L (c s) *
        (LocalizedPoisson.localizedPderiv S L (idx s 0) a *
            LocalizedPoisson.localizedPderiv S L (idx s 1) b -
          LocalizedPoisson.localizedPderiv S L (idx s 1) a *
            LocalizedPoisson.localizedPderiv S L (idx s 0) b) := by
  unfold LocalizedPoisson.bracket
  simp only [pairCoefficients_map]
  exact pairCoefficients_pairing idx (fun s => algebraMap (CubicPolynomial N) L (c s))
    (fun j => LocalizedPoisson.localizedPderiv S L j a)
    (fun j => LocalizedPoisson.localizedPderiv S L j b)
end Localized

namespace LocalizedPairBracket
variable {N : ℕ}
def ratioFieldValue (i j l : Fin N) : ChartLocalization i :=
  (if j=l then 1 else 0) - chartCoordinate i l * (if j=i then 1 else 0)

/-- Clearing one denominator in the actual coordinate derivative. -/
theorem derivative_chartCoordinate_clear (i j l : Fin N) :
    algebraMap (CubicPolynomial N) (ChartLocalization i) (X i) *
        LocalizedPoisson.localizedPderiv (Submonoid.powers (X i)) (ChartLocalization i) j
          (chartCoordinate i l) = ratioFieldValue i j l := by
  classical
  let t := algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)
  let D := LocalizedPoisson.localizedPderiv (Submonoid.powers (X i)) (ChartLocalization i) j
  have hr : t * chartCoordinate i l =
      algebraMap (CubicPolynomial N) (ChartLocalization i) (X l) := by
    dsimp only [t, chartCoordinate]
    rw [mul_comm]
    exact IsLocalization.mk'_spec (ChartLocalization i) (X l) (chartDenominator i)
  have hi : D t = (if j=i then 1 else 0) := by
    simp [D, t, LocalizedPoisson.localizedPderiv, Pi.single_apply, eq_comm]
  have hl : D (algebraMap (CubicPolynomial N) (ChartLocalization i) (X l)) =
      (if j=l then 1 else 0) := by
    simp [D, LocalizedPoisson.localizedPderiv, Pi.single_apply, eq_comm]
  have hd := congrArg D hr
  simp only [Derivation.leibniz, smul_eq_mul, hi, hl] at hd
  exact (eq_sub_iff_add_eq).2 hd

/-- The localized ratio bracket, with both coordinate denominators cleared. -/
theorem ratio_bracket_pairCoefficients_clear {κ : Type*} [Fintype κ]
    (idx : κ → Fin 2 → Fin N) (c : κ → CubicPolynomial N) (i l m : Fin N) :
    algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)^2 *
      LocalizedPoisson.bracket (Submonoid.powers (X i)) (ChartLocalization i)
        (pairCoefficients idx c) (chartCoordinate i l) (chartCoordinate i m) =
      ∑ s, algebraMap (CubicPolynomial N) (ChartLocalization i) (c s) *
        (ratioFieldValue i (idx s 0) l * ratioFieldValue i (idx s 1) m -
          ratioFieldValue i (idx s 1) l * ratioFieldValue i (idx s 0) m) := by
  rw [localized_bracket_pairCoefficients, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  let t := algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)
  let D := LocalizedPoisson.localizedPderiv (Submonoid.powers (X i)) (ChartLocalization i)
  calc
    _ = algebraMap (CubicPolynomial N) (ChartLocalization i) (c s) *
        ((t * D (idx s 0) (chartCoordinate i l)) * (t * D (idx s 1) (chartCoordinate i m)) -
          (t * D (idx s 1) (chartCoordinate i l)) * (t * D (idx s 0) (chartCoordinate i m))) := by ring
    _ = _ := by
      rw [derivative_chartCoordinate_clear, derivative_chartCoordinate_clear,
        derivative_chartCoordinate_clear, derivative_chartCoordinate_clear]
end LocalizedPairBracket
end NcCubic.Geometry
