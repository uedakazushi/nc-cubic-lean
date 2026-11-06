module
public import NcCubic.NondegenerateForm
@[expose] public section
noncomputable section
namespace NcCubic.NondegenerateForm
open Matrix Polynomial

/-- Two determinant pencils, nonzero respectively at their constant and top
coefficients, are simultaneously nonsingular at some scalar. -/
theorem exists_two_pencils_nonsingular
    {F n m : Type*} [Field F] [Infinite F]
    [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (A B : Matrix n n F) (C D : Matrix m m F) (hB : B.det ≠ 0) (hC : C.det ≠ 0) :
    ∃ t : F, (t • A + B).det ≠ 0 ∧ (t • C + D).det ≠ 0 := by
  let p : F[X] := Matrix.det ((X : F[X]) • A.map (Polynomial.C : F →+* F[X]) + B.map (Polynomial.C : F →+* F[X]))
  let q : F[X] := Matrix.det ((X : F[X]) • C.map (Polynomial.C : F →+* F[X]) + D.map (Polynomial.C : F →+* F[X]))
  have hp : p ≠ 0 := by
    intro hz
    have hc := coeff_det_X_add_C_zero A B
    change p.coeff 0 = B.det at hc
    rw [hz, coeff_zero] at hc
    exact hB hc.symm
  have hq : q ≠ 0 := by
    intro hz
    have hc := coeff_det_X_add_C_card C D
    change q.coeff (Fintype.card m) = C.det at hc
    rw [hz, coeff_zero] at hc
    exact hC hc.symm
  have he : ∃ t : F, (p * q).eval t ≠ 0 := by
    by_contra! h
    apply mul_ne_zero hp hq
    apply Polynomial.funext
    intro t
    simpa using h t
  obtain ⟨t, ht⟩ := he
  have ep : p.eval t = (t • A + B).det := by
    change (evalRingHom t) p = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  have eq : q.eval t = (t • C + D).det := by
    change (evalRingHom t) q = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp
    exact mul_comm _ _
  rw [eval_mul, ep, eq] at ht
  exact ⟨t, (mul_ne_zero_iff.mp ht).1, (mul_ne_zero_iff.mp ht).2⟩

/-- Restriction of bilinear forms as a linear map of spaces of forms. -/
def restrictionMap {F V : Type*} [CommRing F] [AddCommGroup V] [Module F V]
    (W : Submodule F V) : LinearMap.BilinForm F V →ₗ[F] LinearMap.BilinForm F W where
  toFun B := B.restrict W
  map_add' := by intro B C; ext x y; rfl
  map_smul' := by intro t B; ext x y; rfl

/-- A basepoint-free symmetric family contains a member nondegenerate on the
ambient space and on any prescribed subspace simultaneously. -/
theorem exists_nondegenerate_and_restrict
    {F V : Type*} [Field F] [Infinite F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (forms : Submodule F (LinearMap.BilinForm F V))
    (hsymm : ∀ H ∈ forms, H.IsSymm)
    (hfree : ∀ v : V, v ≠ 0 → ∃ H ∈ forms, H v v ≠ 0)
    (W : Submodule F V) :
    ∃ B ∈ forms, B.Nondegenerate ∧ (B.restrict W).Nondegenerate := by
  classical
  obtain ⟨B, hB, hb⟩ := exists_nondegenerate forms hsymm hfree
  let restricted := forms.map (restrictionMap W)
  have hrsym : ∀ H ∈ restricted, H.IsSymm := by
    rintro H ⟨D, hD, rfl⟩
    exact (hsymm D hD).restrict W
  have hrfree : ∀ w : W, w ≠ 0 → ∃ H ∈ restricted, H w w ≠ 0 := by
    intro w hw
    have hw' : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
    obtain ⟨D, hD, hd⟩ := hfree w hw'
    exact ⟨D.restrict W, ⟨D, hD, rfl⟩, hd⟩
  obtain ⟨C', hC', hc⟩ := exists_nondegenerate restricted hrsym hrfree
  obtain ⟨C, hC, rfl⟩ := hC'
  let b := Module.finBasis F V
  let c := Module.finBasis F W
  have hbmat := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hb
  have hcmat := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp hc
  obtain ⟨t, ht, htw⟩ := exists_two_pencils_nonsingular
    (LinearMap.BilinForm.toMatrix b C) (LinearMap.BilinForm.toMatrix b B)
    (LinearMap.BilinForm.toMatrix c (C.restrict W))
    (LinearMap.BilinForm.toMatrix c (B.restrict W)) hbmat hcmat
  refine ⟨t • C + B, forms.add_mem (forms.smul_mem t hC) hB, ?_, ?_⟩
  · apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mpr
    simpa only [map_add, map_smul] using ht
  · apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mpr
    convert htw using 1
    congr 1

end NcCubic.NondegenerateForm
