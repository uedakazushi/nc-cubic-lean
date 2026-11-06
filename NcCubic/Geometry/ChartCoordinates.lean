/- Coordinate reindexing for the standard projective charts.
These algebraic definitions do not assume any scheme smoothness. -/
module
public import NcCubic.Geometry.AffineChart
public import Mathlib.Logic.Equiv.Fin.Basic
@[expose] public section
noncomputable section
open MvPolynomial
namespace NcCubic.Geometry.ChartComparison

def pivotReindex {n : ℕ} (j : Fin (n+1)) : Fin (n+1) ≃ Fin n ⊕ Unit :=
  (finSuccEquiv' j).trans (Equiv.optionEquivSumPUnit (Fin n))

@[simp] theorem pivotReindex_pivot {n : ℕ} (j : Fin (n+1)) :
    pivotReindex j j = Sum.inr () := by
  simp [pivotReindex, finSuccEquiv'_at, Equiv.optionEquivSumPUnit]

@[simp] theorem pivotReindex_succAbove {n : ℕ} (j : Fin (n+1)) (a : Fin n) :
    pivotReindex j (j.succAbove a) = Sum.inl a := by
  simp [pivotReindex, finSuccEquiv'_succAbove, Equiv.optionEquivSumPUnit]

variable {R : Type*} [CommRing R]

theorem substitution_eq {n : ℕ} (j : Fin (n+1)) (F : MvPolynomial (Fin (n+1)) R) :
    aeval (fun k => (finSuccEquiv' j k).elim 1 X) F =
      AffineChart.dehomogenize (rename (pivotReindex j) F) := by
  rw [AffineChart.dehomogenize, aeval_rename]
  apply congrArg (fun g : Fin (n+1) → MvPolynomial (Fin n) R => aeval g F)
  funext k
  cases h : finSuccEquiv' j k <;>
    simp [pivotReindex, Equiv.optionEquivSumPUnit, h]

/-- Normalize a point in the j-th chart, written in the original homogeneous coordinates. -/
def chartLift {n : ℕ} (j : Fin (n+1)) (x : Fin n → R) : Fin (n+1) → R :=
  AffineChart.lift x ∘ pivotReindex j

@[simp] theorem chartLift_pivot {n : ℕ} (j : Fin (n+1)) (x : Fin n → R) :
    chartLift j x j = 1 := by simp [chartLift, AffineChart.lift]

@[simp] theorem chartLift_succAbove {n : ℕ} (j : Fin (n+1)) (x : Fin n → R) (a : Fin n) :
    chartLift j x (j.succAbove a) = x a := by simp [chartLift, AffineChart.lift]
end NcCubic.Geometry.ChartComparison
