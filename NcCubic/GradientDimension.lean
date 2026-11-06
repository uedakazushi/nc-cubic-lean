/- The quotient dimension supplied by an isolated homogeneous zero locus. -/
module
public import NcCubic.GradientRadical
public import Mathlib.RingTheory.KrullDimension.Zero
@[expose] public section
noncomputable section
namespace NcCubic.GradientSyzygy
open MvPolynomial
variable {K σ ι : Type*} [Field K] [Finite σ] [IsAlgClosed K]

/-- The quotient by positive homogeneous generators with isolated common zero
has Krull dimension exactly zero. -/
theorem quotient_dimension_zero
    (g : ι → MvPolynomial σ K) {n : ℕ} (hn : n ≠ 0)
    (hg : ∀ i, (g i).IsHomogeneous n)
    (hiso : ∀ x : σ → K, (∀ i, eval x (g i) = 0) → x = 0) :
    ringKrullDim (MvPolynomial σ K ⧸ Ideal.span (Set.range g)) = 0 := by
  let I : Ideal (MvPolynomial σ K) := Ideal.span (Set.range g)
  have hrad : I.radical.IsMaximal := radical_span_isMaximal g hn hg hiso
  have hne : I ≠ ⊤ := by
    intro h
    apply hrad.ne_top
    exact Ideal.radical_eq_top.mpr h
  let : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  apply ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro P hP
  let : P.IsPrime := hP.1.1
  have heq := prime_eq_origin_of_span_le g hn hg hiso P hP.1.2
  rw [heq]
  infer_instance
end NcCubic.GradientSyzygy
