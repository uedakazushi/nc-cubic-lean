/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Raising-chain argument adapted from Mathlib.Algebra.Lie.Sl2,
Copyright (c) 2024 Oliver Nash.
Released under Apache 2.0 license as described in the dependency LICENSE.
-/
module
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.Algebra.Lie.Basis.Base
public import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.LieObstruction
open LieModule Module Set
attribute [local instance 100] LieRing.ofAssociativeRing
variable {K L M : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [AddCommGroup M] [Module K M]
  [LieRingModule L M] [LieModule K L M] [Module.Finite K M]

/-- Raising a specified eigenvector records the precise nonnegative change in weight. -/
theorem primitive_of_eigenvector {h e f : L} (t : IsSl2Triple h e f)
    {μ : K} {m : M} (hm : m ≠ 0) (hh : ⁅h,m⁆ = μ • m) :
    ∃ (n : ℕ) (v : M), t.HasPrimitiveVectorWith v (μ + 2 * n) := by
  let evals (n : ℕ) : K := μ + 2 * (n : K)
  let vecs (n : ℕ) : M := ((toEnd K L M e) ^ n) m
  have hz : ∃ k, vecs k = 0 := by
    by_contra! contra
    have hinj : Function.Injective evals := fun a b hab ↦ by
      simpa [evals, add_right_inj, mul_eq_mul_left_iff, Nat.cast_inj] using hab
    have aux (r : range evals) : (toEnd K L M h).HasEigenvector r (vecs r.property.choose) := by
      set n := r.property.choose
      refine ⟨?_, contra n⟩
      rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply, ← r.property.choose_spec]
      exact t.lie_h_pow_toEnd_e hh _
    have _ := ((toEnd K L M h).eigenvectors_linearIndependent (range evals) _ aux).finite
    exact (Set.infinite_range_of_injective hinj) (Set.toFinite _)
  obtain ⟨n, hn, hn'⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hm hz
  refine ⟨n, vecs n, ⟨hn, t.lie_h_pow_toEnd_e hh n, ?_⟩⟩
  exact (IsSl2Triple.lie_e_pow_toEnd_e n).trans hn'

/-- A nonzero Cartan eigenvalue yields a nonzero primitive weight for one
of the two orientations of an sl₂ triple. -/
theorem nonzero_primitive_of_nonzero_eigenvalue {h e f : L} (t : IsSl2Triple h e f)
    {μ : K} (hμ : μ ≠ 0) {m : M} (hm : m ≠ 0) (hh : ⁅h,m⁆ = μ • m) :
    (∃ (ν : K) (v : M), ν ≠ 0 ∧ t.HasPrimitiveVectorWith v ν) ∨
    (∃ (ν : K) (v : M), ν ≠ 0 ∧ t.symm.HasPrimitiveVectorWith v ν) := by
  obtain ⟨n, v, hv⟩ := primitive_of_eigenvector t hm hh
  by_cases hn : μ + 2 * (n : K) = 0
  · have hn0 : n ≠ 0 := by
      intro h
      simp [h] at hn
      exact hμ hn
    have hh' : ⁅-h,m⁆ = (-μ) • m := by simp [hh]
    obtain ⟨q, w, hw⟩ := primitive_of_eigenvector t.symm hm hh'
    right
    refine ⟨-μ + 2 * (q : K), w, ?_, hw⟩
    have hneg : -μ = 2 * (n : K) := by linear_combination -hn
    rw [hneg, ← mul_add, ← Nat.cast_add]
    exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (by omega))
  · exact Or.inl ⟨μ + 2 * (n : K), v, hn, hv⟩
omit [Module.Finite K M] in
/-- A nontrivial raising operator prevents the Cartan operator being nilpotent. -/
theorem cartan_not_nilpotent_of_raising_ne_zero {h e f : L} (t : IsSl2Triple h e f)
    (he : toEnd K L M e ≠ 0) : ¬ IsNilpotent (toEnd K L M h) := by
  intro hn
  have had := LieAlgebra.ad_nilpotent_of_nilpotent (R := K) hn
  have hev : (LieAlgebra.ad K (Module.End K M) (toEnd K L M h)).HasEigenvector
      (2 : K) (toEnd K L M e) := by
    refine ⟨?_, he⟩
    rw [Module.End.mem_eigenspace_iff]
    change ⁅toEnd K L M h, toEnd K L M e⁆ = _
    rw [← LieHom.map_lie, t.lie_h_e_smul K, map_smul]
  have hz := hev.hasUnifEigenvalue.isNilpotent_of_isNilpotent had
  exact (two_ne_zero : (2 : K) ≠ 0) hz.eq_zero

omit [CharZero K] in
/-- A triangularizable nonnilpotent Cartan operator has a nonzero eigenvalue. -/
theorem nonzero_eigenvalue_of_not_nilpotent [IsTriangularizable K L M]
    (h : L) (hn : ¬ IsNilpotent (toEnd K L M h)) :
    ∃ μ : K, μ ≠ 0 ∧ (toEnd K L M h).HasEigenvalue μ := by
  classical
  by_contra! hc
  have hb (μ : K) (hμ : μ ≠ 0) : (toEnd K L M h).maxGenEigenspace μ = ⊥ := by
    by_contra hb
    exact hc μ hμ ((Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one ENat.top_pos).mp hb)
  have ht : (toEnd K L M h).maxGenEigenspace 0 = ⊤ := by
    have hs := IsTriangularizable.maxGenEigenspace_eq_top (R := K) (L := L) (M := M) h
    have heq : (⨆ μ : K, (toEnd K L M h).maxGenEigenspace μ) =
        (toEnd K L M h).maxGenEigenspace 0 := by
      apply le_antisymm
      · apply iSup_le
        intro μ
        by_cases hm : μ = 0
        · simp [hm]
        · rw [hb μ hm]; exact bot_le
      · exact le_iSup _ 0
    exact heq.symm.trans hs
  apply hn
  refine ⟨Module.finrank K M, ?_⟩
  apply LinearMap.ext
  intro m
  have hm : m ∈ (toEnd K L M h).maxGenEigenspace 0 := ht ▸ Submodule.mem_top
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank,
    Module.End.mem_genEigenspace_nat] at hm
  simpa using hm

/-- A nontrivial raising action produces the nonzero primitive weight needed
for the radical witness, with either orientation permitted. -/
theorem nonzero_primitive_of_raising_ne_zero [IsTriangularizable K L M]
    {h e f : L} (t : IsSl2Triple h e f) (he : toEnd K L M e ≠ 0) :
    (∃ (ν : K) (v : M), ν ≠ 0 ∧ t.HasPrimitiveVectorWith v ν) ∨
    (∃ (ν : K) (v : M), ν ≠ 0 ∧ t.symm.HasPrimitiveVectorWith v ν) := by
  obtain ⟨μ, hμ, heig⟩ := nonzero_eigenvalue_of_not_nilpotent h
    (cartan_not_nilpotent_of_raising_ne_zero t he)
  obtain ⟨m, hm⟩ := heig.exists_hasEigenvector
  exact nonzero_primitive_of_nonzero_eigenvalue t hμ hm.2 hm.apply_eq_smul
/-- A Lie basis detects every nontrivial representation on one of its root
sl₂ triples. The triple may be reversed to orient its highest weight. -/
theorem nonzero_primitive_of_lieBasis {ι : Type*} [Finite ι]
    [IsTriangularizable K L M] {H : LieSubalgebra K L}
    (B : LieAlgebra.Basis ι H) (hnontrivial : ∃ x : L, toEnd K L M x ≠ 0) :
    ∃ h e f : L, ∃ t : IsSl2Triple h e f,
      ∃ (ν : K) (v : M), ν ≠ 0 ∧ t.HasPrimitiveVectorWith v ν := by
  classical
  have hex : ∃ i, toEnd K L M (B.e i) ≠ 0 ∨ toEnd K L M (B.f i) ≠ 0 := by
    by_contra! hc
    have hker : (⊤ : LieSubalgebra K L) ≤ (toEnd K L M).ker.toLieSubalgebra := by
      rw [← B.span_ef, LieSubalgebra.lieSpan_le]
      intro x hx
      rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact (hc i).1
      · exact (hc i).2
    obtain ⟨x,hx⟩ := hnontrivial
    exact hx (hker (LieSubalgebra.mem_top x))
  obtain ⟨i, hi⟩ := hex
  rcases hi with he | hf
  · rcases nonzero_primitive_of_raising_ne_zero (B.sl2 i) he with hp | hp
    · exact ⟨B.h i, B.e i, B.f i, B.sl2 i, hp⟩
    · exact ⟨-B.h i, B.f i, B.e i, (B.sl2 i).symm, hp⟩
  · rcases nonzero_primitive_of_raising_ne_zero (B.sl2 i).symm hf with hp | hp
    · exact ⟨-B.h i, B.f i, B.e i, (B.sl2 i).symm, hp⟩
    · exact ⟨-(-B.h i), B.e i, B.f i, (B.sl2 i).symm.symm, hp⟩
/-- Every nontrivial representation of a finite-dimensional semisimple Lie
algebra over an algebraically closed characteristic-zero field has the
nonzero-weight sl₂ primitive vector used in the radical obstruction. -/
theorem nonzero_primitive_of_semisimple [IsAlgClosed K] [Module.Finite K L]
    [LieAlgebra.IsSemisimple K L] (hnontrivial : ∃ x : L, toEnd K L M x ≠ 0) :
    ∃ h e f : L, ∃ t : IsSl2Triple h e f,
      ∃ (ν : K) (v : M), ν ≠ 0 ∧ t.HasPrimitiveVectorWith v ν := by
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isCartanSubalgebra_engel (K := K) (L := L)
  let := hx
  let H := LieSubalgebra.engel K x
  obtain ⟨b⟩ := (LieAlgebra.IsKilling.rootSystem H).nonempty_base
  obtain ⟨B, _, _⟩ := LieAlgebra.exists_basis_of_base b
  exact nonzero_primitive_of_lieBasis B hnontrivial
end NcCubic.LieObstruction
