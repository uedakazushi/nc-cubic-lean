/- Linear algebra for the basepoint-free pencil argument. -/
module

public import Mathlib.LinearAlgebra.Matrix.Polynomial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Order.SuccPred.Archimedean

@[expose] public section

noncomputable section
namespace NcCubic.NondegenerateForm
open Matrix Polynomial

variable {K n : Type*} [CommRing K] [Fintype n] [DecidableEq n]

/-- If a row of the constant matrix vanishes, its perturbation controls the
linear coefficient of the determinant. No invertibility assumption is needed. -/
theorem coeff_one_det_pencil_of_row_zero (A B : Matrix n n K) (i : n)
    (hi : B i = 0) :
    (Matrix.det ((X : K[X]) • A.map (C : K →+* K[X]) + B.map (C : K →+* K[X]))).coeff 1 =
      Matrix.det (B.updateRow i (A i)) := by
  let M : Matrix n n K[X] := (X : K[X]) • A.map (C : K →+* K[X]) + B.map (C : K →+* K[X])
  have hrow : M i = (X : K[X]) • (A.map (C : K →+* K[X]) i) := by
    funext j
    have hij : B i j = 0 := congrFun hi j
    simp [M, hij]
  have hdet : M.det = (X : K[X]) * (M.updateRow i (A.map (C : K →+* K[X]) i)).det := by
    calc
      M.det = (M.updateRow i (M i)).det := by rw [updateRow_eq_self]
      _ = (M.updateRow i ((X : K[X]) • (A.map (C : K →+* K[X]) i))).det := by rw [hrow]
      _ = _ := Matrix.det_updateRow_smul _ _ _ _
  change M.det.coeff 1 = _
  rw [hdet]
  simp only [coeff_X_mul]
  rw [coeff_zero_eq_eval_zero]
  change (evalRingHom (0 : K)) ((M.updateRow i (A.map (C : K →+* K[X]) i)).det) = _
  rw [RingHom.map_det]
  congr 1
  ext j k
  by_cases h : j = i
  · subst j
    simp
  · simp [Matrix.updateRow, Function.update, h, M]

/-- The bordered minor used to enlarge a nondegenerate restriction: only the
new diagonal entry contributes to its first-order determinant. -/
theorem coeff_one_bordered_pencil (A : Matrix n n K)
    (H : Matrix (PUnit ⊕ n) (PUnit ⊕ n) K) :
    (Matrix.det ((X : K[X]) • H.map (C : K →+* K[X]) +
      (Matrix.fromBlocks (0 : Matrix PUnit PUnit K) 0 0 A).map
        (C : K →+* K[X]))).coeff 1 = H (Sum.inl PUnit.unit) (Sum.inl PUnit.unit) * A.det := by
  rw [coeff_one_det_pencil_of_row_zero H _ (Sum.inl PUnit.unit)]
  · have hupdate :
        (Matrix.fromBlocks (0 : Matrix PUnit PUnit K) 0 0 A).updateRow
          (Sum.inl PUnit.unit) (H (Sum.inl PUnit.unit)) =
        Matrix.fromBlocks (fun i j : PUnit => H (Sum.inl i) (Sum.inl j))
          (fun i j => H (Sum.inl i) (Sum.inr j)) 0 A := by
      ext (i | i) (j | j) <;> simp [Matrix.updateRow, Function.update, Matrix.fromBlocks]
    rw [hupdate]
    calc
      _ = (Matrix.det (fun i j : PUnit => H (Sum.inl i) (Sum.inl j))) * A.det :=
        Matrix.det_fromBlocks_zero₂₁ _ _ _
      _ = _ := congrArg (fun c : K => c * A.det) (Matrix.det_unique _)

  · funext j
    cases j <;> rfl

/-- A nonzero first-order bordered determinant yields an actual invertible
member of the pencil over any infinite field. -/
theorem exists_det_bordered_pencil_ne_zero [IsDomain K] [Infinite K]
    (A : Matrix n n K) (H : Matrix (PUnit ⊕ n) (PUnit ⊕ n) K)
    (hA : A.det ≠ 0) (hH : H (Sum.inl PUnit.unit) (Sum.inl PUnit.unit) ≠ 0) :
    ∃ t : K, (t • H + Matrix.fromBlocks (0 : Matrix PUnit PUnit K) 0 0 A).det ≠ 0 := by
  let B : Matrix (PUnit ⊕ n) (PUnit ⊕ n) K := Matrix.fromBlocks 0 0 0 A
  let p : K[X] := Matrix.det ((X : K[X]) • H.map (C : K →+* K[X]) + B.map (C : K →+* K[X]))
  have hp : p ≠ 0 := by
    intro hz
    have hc := coeff_one_bordered_pencil A H
    change p.coeff 1 = _ at hc
    rw [hz, coeff_zero] at hc
    exact (mul_ne_zero hH hA) hc.symm
  have he : ∃ t : K, p.eval t ≠ 0 := by
    by_contra! h
    apply hp
    apply Polynomial.funext
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := he
  refine ⟨t, ?_⟩
  convert ht using 1
  change _ = (evalRingHom t) p
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [B]
  exact mul_comm _ _

/-- Maximality of a bordered restriction forces every perturbation to vanish
on the radical vector. This is the contradiction used in L0. -/
theorem diagonal_eq_zero_of_all_bordered_pencils_singular [IsDomain K] [Infinite K]
    (A : Matrix n n K) (H : Matrix (PUnit ⊕ n) (PUnit ⊕ n) K)
    (hA : A.det ≠ 0)
    (hs : ∀ t : K, (t • H + Matrix.fromBlocks (0 : Matrix PUnit PUnit K) 0 0 A).det = 0) :
    H (Sum.inl PUnit.unit) (Sum.inl PUnit.unit) = 0 := by
  by_contra hh
  obtain ⟨t, ht⟩ := exists_det_bordered_pencil_ne_zero A H hA hh
  exact ht (hs t)

/-- A basepoint-free linear family enlarges a nonsingular restriction whenever
its matrix has one additional nonzero vector in the radical. The separate
finite-dimensional maximality argument must supply this bordered configuration. -/
theorem exists_form_nondegenerate_on_border
    [IsDomain K] [Infinite K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (forms : Submodule K (LinearMap.BilinForm K V))
    (hfree : ∀ v : V, v ≠ 0 → ∃ H ∈ forms, H v v ≠ 0)
    (B : LinearMap.BilinForm K V) (hB : B ∈ forms)
    (e : PUnit ⊕ n → V) (he : e (Sum.inl PUnit.unit) ≠ 0)
    (A : Matrix n n K) (hA : A.det ≠ 0)
    (hborder : (fun i j => B (e i) (e j)) =
      Matrix.fromBlocks (0 : Matrix PUnit PUnit K) 0 0 A) :
    ∃ D ∈ forms, (Matrix.det (fun i j => D (e i) (e j))) ≠ 0 := by
  obtain ⟨H, hH, hHv⟩ := hfree _ he
  obtain ⟨t, ht⟩ := exists_det_bordered_pencil_ne_zero A
    (fun i j => H (e i) (e j)) hA hHv
  refine ⟨t • H + B, forms.add_mem (forms.smul_mem t hH) hB, ?_⟩
  convert ht using 1
  congr 1
  ext i j
  change t * H (e i) (e j) + B (e i) (e j) =
    t * H (e i) (e j) + Matrix.fromBlocks 0 0 0 A i j
  rw [congrFun (congrFun hborder i) j]

/-- An invertible Gram matrix makes the restriction to the span nondegenerate. -/
theorem nondegenerate_restrict_span_of_det_ne_zero
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι]
    (D : LinearMap.BilinForm F V) (e : ι → V)
    (hd : (Matrix.det (fun i j => D (e i) (e j))) ≠ 0) :
    ∃ _b : Module.Basis ι F (Submodule.span F (Set.range e)),
      (D.restrict (Submodule.span F (Set.range e))).Nondegenerate := by
  let f : V →ₗ[F] (ι → F) := LinearMap.pi (fun i => D (e i))
  have hl : LinearIndependent F e := by
    apply LinearIndependent.of_comp f
    exact Matrix.linearIndependent_cols_of_det_ne_zero hd
  refine ⟨Module.Basis.span hl, ?_⟩
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Module.Basis.span hl)).mpr
  convert hd using 1
  congr 1
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply]
  simp [LinearMap.BilinForm.restrict_apply]

/-- Among all nondegenerate restrictions of forms in a linear family, one has
maximal dimension. This assertion does not yet say that its subspace is all of V. -/
theorem exists_maximal_nondegenerate_restriction
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (forms : Submodule F (LinearMap.BilinForm F V)) :
    ∃ (U : Submodule F V) (B : LinearMap.BilinForm F V), B ∈ forms ∧
      (B.restrict U).Nondegenerate ∧
      ∀ (T : Submodule F V) (D : LinearMap.BilinForm F V), D ∈ forms →
        (D.restrict T).Nondegenerate → Module.finrank F T ≤ Module.finrank F U := by
  let S : Set ℕ := {r | ∃ (U : Submodule F V) (B : LinearMap.BilinForm F V),
    B ∈ forms ∧ (B.restrict U).Nondegenerate ∧ Module.finrank F U = r}
  have hbounded : BddAbove S := by
    refine ⟨Module.finrank F V, ?_⟩
    rintro r ⟨U, B, hB, hU, rfl⟩
    exact Submodule.finrank_le U
  have hnonempty : S.Nonempty := by
    refine ⟨0, ⊥, 0, forms.zero_mem, ?_, ?_⟩
    · constructor <;> intro x hx <;> exact Subsingleton.elim _ _
    · simp
  obtain ⟨r, hr, hmax⟩ := hbounded.exists_isGreatest_of_nonempty hnonempty
  obtain ⟨U, B, hB, hU, hdim⟩ := hr
  refine ⟨U, B, hB, hU, ?_⟩
  intro T D hD hT
  rw [hdim]
  exact hmax ⟨T, D, hD, hT, rfl⟩

/-- A basepoint-free linear system of symmetric bilinear forms on a finite
 dimensional vector space over an infinite field contains a nondegenerate form.
 The proof uses maximal nondegenerate restrictions and bordered pencil minors. -/
theorem exists_nondegenerate
    {F V : Type*} [Field F] [Infinite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (forms : Submodule F (LinearMap.BilinForm F V))
    (hsymm : ∀ H ∈ forms, H.IsSymm)
    (hfree : ∀ v : V, v ≠ 0 → ∃ H ∈ forms, H v v ≠ 0) :
    ∃ B ∈ forms, B.Nondegenerate := by
  classical
  obtain ⟨U, B, hB, hU, hmax⟩ := exists_maximal_nondegenerate_restriction forms
  have hsym := hsymm B hB
  have htop : U = ⊤ := by
    by_contra hproper
    have hc := B.isCompl_orthogonal_of_restrict_nondegenerate hsym.isRefl hU
    have ho : B.orthogonal U ≠ ⊥ := by
      intro h
      exact hproper (eq_top_of_isCompl_bot (h ▸ hc))
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp ho
    let b := Module.finBasis F U
    let e : PUnit.{1} ⊕ Fin (Module.finrank F U) → V :=
      Sum.elim (fun _ => v) (fun j => (b j : V))
    let A : Matrix (Fin (Module.finrank F U)) (Fin (Module.finrank F U)) F :=
      fun i j => B (b i) (b j)
    have hA : A.det ≠ 0 := by
      have ha := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hU
      convert ha using 1
      congr 1
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      rfl
    have hvan : ∀ i, B (b i) v = 0 := fun i => hv _ (b i).property
    have hgram : (fun i j => B (e i) (e j)) =
        Matrix.fromBlocks (fun _ _ : PUnit.{1} => B v v) 0 0 A := by
      ext (i | i) (j | j)
      · rfl
      · change B v (b j) = 0
        rw [hsym.eq]
        exact hvan j
      · exact hvan i
      · rfl
    have hcontra : ∀ D ∈ forms, (Matrix.det (fun i j => D (e i) (e j))) = 0 := by
      intro D hD
      by_contra hd
      obtain ⟨basis, hnd⟩ := nondegenerate_restrict_span_of_det_ne_zero D e hd
      have hm := hmax _ D hD hnd
      rw [Module.finrank_eq_card_basis basis] at hm
      simp only [Fintype.card_sum, Fintype.card_punit, Fintype.card_fin] at hm
      omega
    have hdiag : B v v = 0 := by
      have hd := hcontra B hB
      rw [hgram] at hd
      have heq := Matrix.det_fromBlocks_zero₂₁
        (fun _ _ : PUnit.{1} => B v v)
        (0 : Matrix PUnit.{1} (Fin (Module.finrank F U)) F) A
      have hsingle : Matrix.det (fun _ _ : PUnit.{1} => B v v) = B v v :=
        Matrix.det_unique _
      rw [heq, hsingle] at hd
      exact (mul_eq_zero.mp hd).resolve_right hA
    have hborder : (fun i j => B (e i) (e j)) =
        Matrix.fromBlocks (0 : Matrix PUnit.{1} PUnit.{1} F) 0 0 A := by
      rw [hgram]
      congr 1
      ext i j
      exact hdiag
    obtain ⟨D, hD, hd⟩ := exists_form_nondegenerate_on_border forms hfree B hB e hv0 A hA hborder
    exact hd (hcontra D hD)
  subst U
  refine ⟨B, hB, ?_⟩
  constructor
  · intro x hx
    have h := hU.1 ⟨x, Submodule.mem_top⟩ (fun y => hx y)
    exact congrArg Subtype.val h
  · intro x hx
    have h := hU.2 ⟨x, Submodule.mem_top⟩ (fun y => hx y)
    exact congrArg Subtype.val h

end NcCubic.NondegenerateForm
