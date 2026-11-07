/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Statement
public import Mathlib.LinearAlgebra.Basis.Basic
@[expose] public noncomputable section
namespace NcCubic
open scoped BigOperators
/-- A nonempty block volume form is a nonzero alternating tensor. -/
theorem blockTrivector_ne_zero {N k m : ℕ} (P : Trivector N)
    (hk : 1 ≤ k) (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (h : HasBlockTrivector P b) : P ≠ 0 := by
  classical
  let s₀ : Fin k := ⟨0,by omega⟩
  let α : Fin 3 → Covector N := fun i => b.coord (Sum.inl (s₀,i))
  have hd (s : Fin k) :
      Matrix.det (fun i j : Fin 3 => α i (b (Sum.inl (s,j)))) = if s=s₀ then 1 else 0 := by
    by_cases hs : s=s₀
    · subst s
      have hm : (fun i j : Fin 3 => α i (b (Sum.inl (s₀,j)))) = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
        ext i j
        simp [α,Module.Basis.coord_apply,Matrix.one_apply,Finsupp.single_apply,eq_comm]
      rw [hm]
      simp
    · have hm : (fun i j : Fin 3 => α i (b (Sum.inl (s,j)))) = (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
        ext i j
        simp [α,Module.Basis.coord_apply,Ne.symm hs]
      rw [hm]
      simp [hs]
  have hp : P α = 1 := by
    rw [h]
    simp_rw [hd]
    simp
  intro hP
  rw [hP] at hp
  exact zero_ne_one hp

/-- Every tensor in the requested block normal form is nonzero. -/
theorem normalForm_trivector_ne_zero {N : ℕ} {F : CubicPolynomial N} {P : Trivector N}
    (h : HasBlockNormalForm F P) : P ≠ 0 := by
  obtain ⟨k,m,hk,_,b,_,_,hb,_⟩ := h
  exact blockTrivector_ne_zero P hk b hb
end NcCubic
