module
public import NcCubic.Statement
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.NormNum
@[expose] public section
noncomputable section
namespace NcCubic.PolynomialBlocks
open MvPolynomial
open scoped BigOperators

/-- A vanished mixed derivative rules out every monomial using both variables. -/
theorem coeff_zero_of_mixed_derivative_zero {σ : Type*} [DecidableEq σ]
    (F : MvPolynomial σ ℂ) (i j : σ) (hij : i ≠ j)
    (h : pderiv i (pderiv j F) = 0) (d : σ →₀ ℕ)
    (hi : d i ≠ 0) (hj : d j ≠ 0) : F.coeff d = 0 := by
  let d' := d - Finsupp.single j 1
  let m := d' - Finsupp.single i 1
  have hdj : d' + Finsupp.single j 1 = d :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj))
  have hi' : d' i ≠ 0 := by simpa [d', Finsupp.single_apply, hij.symm] using hi
  have hmi : m + Finsupp.single i 1 = d' :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi'))
  have hc := congrArg (fun p : MvPolynomial σ ℂ => p.coeff m) h
  rw [coeff_pderiv, coeff_pderiv, hmi, hdj] at hc
  have hlast : (↑(m i) + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m i)
  have hmiddle : (↑(d' j) + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d' j)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right hlast)).resolve_right hmiddle

theorem blockVariable_injective {k m : ℕ} (s : Fin k) :
    Function.Injective (blockVariable (m := m) s) := by
  intro a b hab
  cases a <;> cases b <;> simp_all [blockVariable]

/-- Every surviving monomial uses at most one active block. -/
theorem monomial_support_in_block {k m : ℕ} (hk : 1 ≤ k)
    (F : MvPolynomial (BlockIndex k m) ℂ)
    (hmixed : ∀ (s t : Fin k), s ≠ t → ∀ i j,
      pderiv (Sum.inl (s,i)) (pderiv (Sum.inl (t,j)) F) = 0)
    (d : BlockIndex k m →₀ ℕ) (hd : d ∈ F.support) :
    ∃ s : Fin k, (↑d.support : Set (BlockIndex k m)) ⊆ Set.range (blockVariable s) := by
  classical
  by_cases ha : ∃ (s : Fin k) (i : Fin 3), d (Sum.inl (s,i)) ≠ 0
  · obtain ⟨s,i,hi⟩ := ha
    refine ⟨s, ?_⟩
    intro x hx
    rcases x with ⟨t,j⟩ | u
    · have ht : t = s := by
        by_contra hts
        have hc := coeff_zero_of_mixed_derivative_zero F (Sum.inl (s,i))
          (Sum.inl (t,j)) (by intro h; cases h; exact hts rfl)
          (hmixed s t (Ne.symm hts) i j) d hi (Finsupp.mem_support_iff.mp hx)
        exact (mem_support_iff.mp hd) hc
      subst t
      exact ⟨Sum.inl j, rfl⟩
    · exact ⟨Sum.inr u, rfl⟩
  · refine ⟨⟨0,hk⟩, ?_⟩
    intro x hx
    rcases x with ⟨t,j⟩ | u
    · exact False.elim (ha ⟨t,j,Finsupp.mem_support_iff.mp hx⟩)
    · exact ⟨Sum.inr u, rfl⟩

/-- A monomial supported on one block is the renaming of a local monomial. -/
theorem local_monomial {k m n : ℕ} (s : Fin k) (d : BlockIndex k m →₀ ℕ)
    (a : ℂ) (hd : (↑d.support : Set (BlockIndex k m)) ⊆ Set.range (blockVariable s))
    (hn : d.degree = n) :
    ∃ f : MvPolynomial (Fin 3 ⊕ Fin m) ℂ,
      f.IsHomogeneous n ∧ rename (blockVariable s) f = monomial d a := by
  let e := Finsupp.comapDomain (blockVariable s) d (blockVariable_injective s).injOn
  have hrename : rename (blockVariable s) (monomial e a) = monomial d a := by
    rw [rename_monomial, Finsupp.mapDomain_comapDomain _ (blockVariable_injective s) d hd]
  refine ⟨monomial e a, ?_, hrename⟩
  apply (IsHomogeneous.rename_isHomogeneous_iff (blockVariable_injective s)).mp
  rw [hrename]
  exact isHomogeneous_monomial a hn

/-- Vanishing mixed active derivatives gives the polynomial block decomposition.
Purely central monomials are assigned to block zero; no smoothness is needed. -/
theorem decomposition_of_mixed_derivatives {k m n : ℕ} (hk : 1 ≤ k)
    (F : MvPolynomial (BlockIndex k m) ℂ) (hF : F.IsHomogeneous n)
    (hmixed : ∀ (s t : Fin k), s ≠ t → ∀ i j,
      pderiv (Sum.inl (s,i)) (pderiv (Sum.inl (t,j)) F) = 0) :
    ∃ f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) ℂ,
      (∀ s, (f s).IsHomogeneous n) ∧
      F = ∑ s, rename (blockVariable s) (f s) := by
  classical
  let D := {d : BlockIndex k m →₀ ℕ // d ∈ F.support}
  let owner (d : D) : Fin k :=
    if ∀ (t : Fin k) (j : Fin 3), d.val (Sum.inl (t,j)) = 0 then ⟨0,hk⟩
    else (monomial_support_in_block hk F hmixed d.val d.property).choose
  have howner (d : D) : (↑d.val.support : Set (BlockIndex k m)) ⊆
      Set.range (blockVariable (owner d)) := by
    by_cases hc : ∀ (t : Fin k) (j : Fin 3), d.val (Sum.inl (t,j)) = 0
    · intro x hx
      rcases x with ⟨t,j⟩ | u
      · exact False.elim ((Finsupp.mem_support_iff.mp hx) (hc t j))
      · exact ⟨Sum.inr u, rfl⟩
    · simpa only [owner, ite_eq_right_iff.mpr (fun h => (hc h).elim)] using
        (monomial_support_in_block hk F hmixed d.val d.property).choose_spec
  have hlocal (d : D) : ∃ f : MvPolynomial (Fin 3 ⊕ Fin m) ℂ,
      f.IsHomogeneous n ∧ rename (blockVariable (owner d)) f =
        monomial d.val (F.coeff d.val) := by
    exact local_monomial (owner d) d.val (F.coeff d.val) (howner d)
      (by change (∑ i ∈ d.val.support, d.val i) = n
          exact (hF.degree_eq_sum_deg_support d.property).symm)
  choose piece hhom hren using hlocal
  let f (s : Fin k) := ∑ d : D, if owner d = s then piece d else 0
  refine ⟨f, ?_, ?_⟩
  · intro s
    apply IsHomogeneous.sum
    intro d _
    split_ifs
    · exact hhom d
    · exact isHomogeneous_zero _ _ _
  · have hsum : ∑ s, rename (blockVariable s) (f s) =
        ∑ d : D, monomial d.val (F.coeff d.val) := by
      simp only [f, map_sum, apply_ite (rename _), map_zero]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_eq_single (owner d)]
      · simp only [ite_true, hren]
      · intro s _ hs
        simp only [ite_eq_right_iff]
        intro h
        exact (hs h.symm).elim
      · simp
    rw [hsum]
    change F = ∑ d ∈ F.support.attach, monomial d.val (F.coeff d.val)
    rw [Finset.sum_attach F.support (fun d => monomial d (F.coeff d))]
    exact F.as_sum
end NcCubic.PolynomialBlocks
