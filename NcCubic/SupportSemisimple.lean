/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.SupportConstruction
public import NcCubic.RadicalElimination
public import Mathlib.Analysis.Complex.Polynomial.Basic
@[expose] public section
noncomputable section
namespace NcCubic.LieObstruction
variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]

/-- Bracket spanning and a zero vector center convert to the standard
perfectness and center-ideal hypotheses of radical elimination. -/
theorem semisimple_of_bracket_span_center_zero
    (hspan : Submodule.span K (Set.range (fun p : L × L => ⁅p.1,p.2⁆)) = ⊤)
    (hcenter : ∀ x : L, (∀ y : L, ⁅x,y⁆ = 0) → x = 0)
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, Compatible H) (hfree : BasepointFree forms) :
    LieAlgebra.IsSemisimple K L := by
  have hset : {⁅a,b⁆ | (a : L) (b : L)} =
      Set.range (fun p : L × L => ⁅p.1,p.2⁆) := by
    ext x
    constructor
    · rintro ⟨a,b,rfl⟩; exact ⟨(a,b),rfl⟩
    · rintro ⟨⟨a,b⟩,rfl⟩; exact ⟨a,b,rfl⟩
  have hp : LieAlgebra.derivedSeries K L 1 = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have hm : x ∈ (LieAlgebra.derivedSeries K L 1 : Submodule K L) := by
      rw [LieAlgebra.coe_derivedSeries_one_eq, hset, hspan]
      trivial
    exact hm
  have hc : LieAlgebra.center K L = ⊥ := by
    rw [LieSubmodule.eq_bot_iff]
    intro x hx
    apply hcenter x
    intro y
    have hx' := (LieModule.mem_maxTrivSubmodule K L L x).mp hx y
    simpa only [hx', neg_zero] using (lie_skew x y).symm
  let : LieAlgebra.HasTrivialRadical K L :=
    ⟨radical_eq_bot_of_compatible_basepointFree hp hc forms hcompatible hfree⟩
  infer_instance
end NcCubic.LieObstruction

namespace NcCubic.SupportConstruction
open HessianCompatibility
variable {N : ℕ}

/-- The actual support Lie algebra built from the compatible metric is
semisimple; the metric and forms are the concrete restricted ambient forms. -/
theorem support_isSemisimple (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hmem : B ∈ compatibleForms P)
    (hB : B.Nondegenerate) (hBr : (B.restrict (support P)).Nondegenerate)
    (hfree : ∀ v : CoordinateSpace N, v ≠ 0 → ∃ H ∈ compatibleForms P, H v v ≠ 0) :
    let := supportLieRing P B (compatibleForms_isSymm P B hmem) hBr hmem.1
    let := supportLieAlgebra P B (compatibleForms_isSymm P B hmem) hBr hmem.1
    LieAlgebra.IsSemisimple ℂ (support P) := by
  let := supportLieRing P B (compatibleForms_isSymm P B hmem) hBr hmem.1
  let := supportLieAlgebra P B (compatibleForms_isSymm P B hmem) hBr hmem.1
  apply LieObstruction.semisimple_of_bracket_span_center_zero
    (restricted_bracket_span_eq_top P B (compatibleForms_isSymm P B hmem) hB hBr)
    (support_center_zero P B (compatibleForms_isSymm P B hmem) hB hBr)
    (Set.range (fun H : compatibleForms P => H.val.restrict (support P)))
  · rintro H ⟨H',rfl⟩
    exact restricted_obstruction_compatible P B H'.val
      (compatibleForms_isSymm P B hmem) hBr hmem.1 H'.property.1
  · intro v hv
    obtain ⟨H,hH,hvH⟩ := restricted_family_basepoint_free P hfree v hv
    exact ⟨H.restrict (support P), ⟨⟨H,hH⟩,rfl⟩, hvH⟩

/-- Basepoint-freeness supplies both the metric and the semisimple support
Lie structure, without any semisimplicity hypothesis. -/
theorem exists_support_semisimple_data (P : Trivector N)
    (hfree : ∀ v : CoordinateSpace N, v ≠ 0 → ∃ H ∈ compatibleForms P, H v v ≠ 0) :
    ∃ (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hmem : B ∈ compatibleForms P)
      (_hB : B.Nondegenerate) (hBr : (B.restrict (support P)).Nondegenerate),
      let := supportLieRing P B (compatibleForms_isSymm P B hmem) hBr hmem.1
      let := supportLieAlgebra P B (compatibleForms_isSymm P B hmem) hBr hmem.1
      LieAlgebra.IsSemisimple ℂ (support P) := by
  obtain ⟨B,hmem,hB,hBr⟩ := exists_support_metric P hfree
  exact ⟨B,hmem,hB,hBr,support_isSemisimple P B hmem hB hBr hfree⟩
end NcCubic.SupportConstruction
