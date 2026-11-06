/- The Nullstellensatz bridge from isolated gradient zero to a maximal radical.
This does not yet establish that the gradient sequence is regular. -/
module
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
@[expose] public section
noncomputable section
namespace NcCubic.GradientSyzygy
open MvPolynomial
variable {K σ ι : Type*} [Field K]

/-- Positive homogeneous generators with no nonzero common zero cut out the origin. -/
theorem zeroLocus_span_eq_singleton_zero
    (g : ι → MvPolynomial σ K) {n : ℕ} (hn : n ≠ 0)
    (hg : ∀ i, (g i).IsHomogeneous n)
    (hiso : ∀ x : σ → K, (∀ i, eval x (g i) = 0) → x = 0) :
    zeroLocus K (Ideal.span (Set.range g)) = {0} := by
  classical
  rw [zeroLocus_span]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
    Set.mem_singleton_iff]
  constructor
  · intro hx
    apply hiso x
    intro i
    simpa using hx i
  · intro hx i
    subst x
    have hc : (g i).coeff 0 = 0 := (hg i).coeff_eq_zero (by simpa using hn.symm)
    simpa [aeval_zero, constantCoeff] using hc

/-- Nullstellensatz turns the isolated-zero condition into an exact radical ideal equality. -/
theorem radical_span_eq_vanishingIdeal_zero [Finite σ] [IsAlgClosed K]
    (g : ι → MvPolynomial σ K) {n : ℕ} (hn : n ≠ 0)
    (hg : ∀ i, (g i).IsHomogeneous n)
    (hiso : ∀ x : σ → K, (∀ i, eval x (g i) = 0) → x = 0) :
    (Ideal.span (Set.range g)).radical = vanishingIdeal K ({0} : Set (σ → K)) := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K),
    zeroLocus_span_eq_singleton_zero g hn hg hiso]
/-- In particular the isolated-zero ideal has maximal radical. -/
theorem radical_span_isMaximal [Finite σ] [IsAlgClosed K]
    (g : ι → MvPolynomial σ K) {n : ℕ} (hn : n ≠ 0)
    (hg : ∀ i, (g i).IsHomogeneous n)
    (hiso : ∀ x : σ → K, (∀ i, eval x (g i) = 0) → x = 0) :
    (Ideal.span (Set.range g)).radical.IsMaximal := by
  rw [radical_span_eq_vanishingIdeal_zero g hn hg hiso]
  infer_instance

/-- There is a unique prime above an isolated homogeneous zero ideal. -/
theorem prime_eq_origin_of_span_le [Finite σ] [IsAlgClosed K]
    (g : ι → MvPolynomial σ K) {n : ℕ} (hn : n ≠ 0)
    (hg : ∀ i, (g i).IsHomogeneous n)
    (hiso : ∀ x : σ → K, (∀ i, eval x (g i) = 0) → x = 0)
    (P : Ideal (MvPolynomial σ K)) [hP : P.IsPrime]
    (hIP : Ideal.span (Set.range g) ≤ P) :
    P = vanishingIdeal K ({0} : Set (σ → K)) := by
  have hle : (Ideal.span (Set.range g)).radical ≤ P := by
    simpa only [hP.radical] using Ideal.radical_mono hIP
  have heq := (radical_span_isMaximal g hn hg hiso).eq_of_le hP.ne_top hle
  rw [radical_span_eq_vanishingIdeal_zero g hn hg hiso] at heq
  exact heq.symm

/-- The geometric gradient condition supplies the radical equality for cubics. -/
theorem cubic_gradient_radical [Finite σ] [IsAlgClosed K]
    (F : MvPolynomial σ K) (hF : F.IsHomogeneous 3)
    (hiso : ∀ x : σ → K, (∀ i, eval x (pderiv i F) = 0) → x = 0) :
    (Ideal.span (Set.range fun i => pderiv i F)).radical =
      vanishingIdeal K ({0} : Set (σ → K)) := by
  apply radical_span_eq_vanishingIdeal_zero (n := 2) _ (by decide) _ hiso
  intro i
  simpa using (hF.pderiv (i := i))
end NcCubic.GradientSyzygy
