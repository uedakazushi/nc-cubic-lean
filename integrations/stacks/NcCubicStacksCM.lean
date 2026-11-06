import StacksFrontier.RingTheory.CohenMacaulay.MvPolynomial
import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence.DimensionCriterion

/-!
# Optional Cohen–Macaulay API check

This target is intentionally excluded from `defaultTargets`: its transitive
imports may be expensive. These checks inspect upstream interfaces, not a proof
that the gradient of a smooth homogeneous cubic is a regular sequence.

Upstream Stacks tags: 0AAI, 00ND, 02JN.
-/

#check Module.IsCohenMacaulay.mvPolynomial_of_isBaseChange
#check Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial
#check Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim

#print axioms Module.IsCohenMacaulay.mvPolynomial_of_isBaseChange
#print axioms Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime_mvPolynomial
#print axioms Module.IsMaximalCohenMacaulay.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim
