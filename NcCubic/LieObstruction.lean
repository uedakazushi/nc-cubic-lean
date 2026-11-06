/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Isotropy obstructions for compatible bilinear forms

This file proves the substitutions in equation (3.2) used in Steps 2 and 3
of Lemma 3.2 of `cubic_poisson_paper_20261104.pdf`, printed pages 6–7.
The existence of the radical or highest-root witnesses is a separate,
currently open obligation in the classification proof.

Symmetry of the bilinear form is unnecessary for these two calculations.
The proofs therefore apply to any bilinear form satisfying (3.2).
-/

@[expose] public section

namespace NcCubic.LieObstruction

variable {K : Type*} {L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

/-- The compatibility identity (3.2) from the source paper. -/
def Compatible (H : L →ₗ[K] L →ₗ[K] K) : Prop :=
  ∀ a b c d : L,
    H ⁅a, b⁆ ⁅c, d⁆ + H ⁅b, c⁆ ⁅a, d⁆ + H ⁅c, a⁆ ⁅b, d⁆ = 0

/-- A family of quadratic evaluations has no nonzero common zero. -/
def BasepointFree (forms : Set (L →ₗ[K] L →ₗ[K] K)) : Prop :=
  ∀ v : L, v ≠ 0 → ∃ H ∈ forms, H v v ≠ 0

/-- The algebraic substitution used in §3.3 to eliminate mixed Hessian
pairings between different blocks. Extending this from brackets to whole
perfect ideals requires the separate spanning argument. -/
theorem cross_bracket_pairing_zero (H : L →ₗ[K] L →ₗ[K] K)
    (hH : Compatible H) (a b c d : L)
    (hbc : ⁅b, c⁆ = 0) (hca : ⁅c, a⁆ = 0) : H ⁅a, b⁆ ⁅c, d⁆ = 0 := by
  simpa [hbc, hca] using hH a b c d

/-- Step 2 of Lemma 3.2: the displayed radical witness is isotropic for every
compatible form. This does not construct the witness from a nonzero radical. -/
theorem radical_witness_isotropic (H : L →ₗ[K] L →ₗ[K] K) (hH : Compatible H)
    (h v e w : L) (c : K) (hc : c ≠ 0)
    (hhv : ⁅h, v⁆ = c • v) (hew : ⁅e, w⁆ = v)
    (hev : ⁅e, v⁆ = 0) (hvw : ⁅v, w⁆ = 0) : H v v = 0 := by
  have hve : ⁅v, e⁆ = 0 := by
    simpa [hev] using (lie_skew v e).symm
  have hmul : c * H v v = 0 := by
    simpa [hhv, hew, hve, hvw, smul_eq_mul] using hH h v e w
  exact (mul_eq_zero.mp hmul).resolve_left hc

/-- Step 3 of Lemma 3.2: the displayed highest-root witness is isotropic for
every compatible form. Its root-theoretic existence is not assumed proved. -/
theorem highest_root_witness_isotropic (H : L →ₗ[K] L →ₗ[K] K)
    (hH : Compatible H) (a b h v : L) (c : K) (hc : c ≠ 0)
    (hab : ⁅a, b⁆ = v) (hhv : ⁅h, v⁆ = c • v)
    (hav : ⁅a, v⁆ = 0) (hbv : ⁅b, v⁆ = 0) : H v v = 0 := by
  have hmul : c * H v v = 0 := by
    simpa [hab, hhv, hav, hbv, smul_eq_mul] using hH a b h v
  exact (mul_eq_zero.mp hmul).resolve_left hc

/-- A basepoint-free family of compatible forms rules out a nonzero radical
witness of the shape used by the paper. -/
theorem no_radical_witness
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, Compatible H) (hfree : BasepointFree forms)
    (h v e w : L) (c : K) (hv : v ≠ 0) (hc : c ≠ 0)
    (hhv : ⁅h, v⁆ = c • v) (hew : ⁅e, w⁆ = v)
    (hev : ⁅e, v⁆ = 0) (hvw : ⁅v, w⁆ = 0) : False := by
  obtain ⟨H, hH, hnonzero⟩ := hfree v hv
  exact hnonzero
    (radical_witness_isotropic H (hcompatible H hH) h v e w c hc hhv hew hev hvw)

/-- A basepoint-free family of compatible forms rules out the nonzero
highest-root witness used in Step 3 of the paper. -/
theorem no_highest_root_witness
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, Compatible H) (hfree : BasepointFree forms)
    (a b h v : L) (c : K) (hv : v ≠ 0) (hc : c ≠ 0)
    (hab : ⁅a, b⁆ = v) (hhv : ⁅h, v⁆ = c • v)
    (hav : ⁅a, v⁆ = 0) (hbv : ⁅b, v⁆ = 0) : False := by
  obtain ⟨H, hH, hnonzero⟩ := hfree v hv
  exact hnonzero
    (highest_root_witness_isotropic H (hcompatible H hH) a b h v c hc hab hhv hav hbv)

end NcCubic.LieObstruction
