import StacksFrontier.RingTheory.Koszul.Regular
import StacksFrontier.RingTheory.Koszul.Relations

/-!
# Focused Stacks integration: regular sequences and first syzygies

These adapters use the fixed AxiomMath/Stacks revision in `lakefile.toml`.
They do not assert regularity of the gradient of a smooth cubic.
Connecting cubic smoothness to regularity, and extracting the degree-zero and
degree-one syzygy consequences, remain separate obligations.
-/

open scoped BigOperators

namespace NcCubicStacks

universe u

variable {R : Type u} [CommRing R] {r : ℕ}

/-- A regular sequence has vanishing first Koszul homology. -/
theorem h1Regular_of_regular (f : Fin r → R)
    (h : RingTheory.Sequence.IsRegular R (List.ofFn f)) :
    Koszul.IsH1Regular f := by
  have hk : Koszul.IsKoszulRegular f :=
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
      (R := R) (M := R) (f := f)).2.2 h
  exact hk.isH1Regular

/-- Every first syzygy of a regular sequence lies in the span of its
Koszul relations. This is the generic algebraic input for paper Lemma 2.1. -/
theorem syzygy_mem_relSpan_of_regular (f : Fin r → R)
    (h : RingTheory.Sequence.IsRegular R (List.ofFn f))
    (a : Fin r → R) (ha : ∑ i, a i * f i = 0) :
    a ∈ Koszul.relSpan f := by
  exact (Koszul.isH1Regular_iff_forall f).mp
    (h1Regular_of_regular f h) a ha

end NcCubicStacks

#check Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
#check Koszul.isH1Regular_iff_forall

#print axioms NcCubicStacks.h1Regular_of_regular
#print axioms NcCubicStacks.syzygy_mem_relSpan_of_regular
