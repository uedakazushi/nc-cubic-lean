module
public import NcCubic.HessianCompatibility
public import NcCubic.SupportLie
public import NcCubic.LieObstruction
public import NcCubic.NondegenerateRestriction
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace NcCubic.SupportConstruction
open HessianCompatibility
variable {N : ℕ}

/-- Raise two covectors with a symmetric metric and contract the trivector. -/
def raisedBracket (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) :
    CoordinateSpace N →ₗ[ℂ] CoordinateSpace N →ₗ[ℂ] CoordinateSpace N where
  toFun x := (contraction P (B x)).comp B
  map_add' := by intro x y; ext z a; simp
  map_smul' := by intro c x; ext z a; simp

@[simp] theorem raisedBracket_apply (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (x y : CoordinateSpace N) :
    raisedBracket P B x y = contraction P (B x) (B y) := rfl

theorem raisedBracket_self (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (x : CoordinateSpace N) :
    raisedBracket P B x x = 0 := by
  ext a
  exact P.map_eq_zero_of_eq ![B x, B x, coordinateCovector a]
    (i := (0 : Fin 3)) (j := 1) rfl (by decide)

theorem trivector_cyclic (P : Trivector N) (α β γ : Covector N) :
    P ![α, β, γ] = P ![β, γ, α] := by
  have h1 := P.map_swap ![α, β, γ] (show (0 : Fin 3) ≠ 1 by decide)
  have h2 := P.map_swap ![β, α, γ] (show (1 : Fin 3) ≠ 2 by decide)
  have hv1 : (![α, β, γ] ∘ Equiv.swap (0 : Fin 3) 1) = ![β, α, γ] := by
    funext i; fin_cases i <;> norm_num [Equiv.swap_apply_def]
  have hv2 : (![β, α, γ] ∘ Equiv.swap (1 : Fin 3) 2) = ![β, γ, α] := by
    funext i; fin_cases i <;> norm_num [Equiv.swap_apply_def]
  rw [hv1] at h1
  rw [hv2, h1, neg_neg] at h2
  exact h2.symm

theorem pair_raisedBracket (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (x y z : CoordinateSpace N) :
    B (raisedBracket P B x y) z = P ![B x, B y, B z] := by
  rw [hsym.eq, raisedBracket_apply, contraction_eval]

theorem raisedBracket_invariant (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (x y z : CoordinateSpace N) :
    B (raisedBracket P B x y) z = B x (raisedBracket P B y z) := by
  rw [pair_raisedBracket P B hsym, raisedBracket_apply, contraction_eval]
  exact trivector_cyclic P _ _ _

theorem raisedBracket_compatible (P : Trivector N)
    (B H : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hH : HessianCompatibility.Compatible P H) :
    SupportLie.Compatible (raisedBracket P B) H := by
  intro a b c d
  exact hH ![B a, B b, B c, B d]

@[instance_reducible]
def lieRing (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate) (hK : HessianCompatibility.Compatible P B) :
    LieRing (CoordinateSpace N) :=
  SupportLie.lieRingOfCompatible (raisedBracket P B) B hB
    (raisedBracket_self P B) (raisedBracket_invariant P B hsym)
    (raisedBracket_compatible P B B hK)

@[instance_reducible]
def lieAlgebra (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate) (hK : HessianCompatibility.Compatible P B) :
    @LieAlgebra ℂ (CoordinateSpace N) inferInstance (lieRing P B hsym hB hK) :=
  SupportLie.lieAlgebraOfCompatible (raisedBracket P B) B hB
    (raisedBracket_self P B) (raisedBracket_invariant P B hsym)
    (raisedBracket_compatible P B B hK)

/-- The intrinsic support is the span of all two-covector contractions. -/
def support (P : Trivector N) : Submodule ℂ (CoordinateSpace N) :=
  Submodule.span ℂ (Set.range (fun p : Covector N × Covector N => contraction P p.1 p.2))

theorem bracket_span_eq_support (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hB : B.Nondegenerate) :
    Submodule.span ℂ (Set.range (fun p : CoordinateSpace N × CoordinateSpace N =>
      raisedBracket P B p.1 p.2)) = support P := by
  apply congrArg (Submodule.span ℂ)
  ext v
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact ⟨(B x, B y), rfl⟩
  · rintro ⟨⟨α, β⟩, rfl⟩
    refine ⟨((B.toDual hB).symm α, (B.toDual hB).symm β), ?_⟩
    change contraction P (B ((B.toDual hB).symm α)) (B ((B.toDual hB).symm β)) = _
    have hα : B ((B.toDual hB).symm α) = α := (B.toDual hB).apply_symm_apply α
    have hβ : B ((B.toDual hB).symm β) = β := (B.toDual hB).apply_symm_apply β
    rw [hα, hβ]

/-- The center of the ambient metric bracket is precisely the metric-orthogonal
complement of the trivector support. Jacobi is not needed for this identity. -/
theorem central_iff_orthogonal_support (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (hB : B.Nondegenerate) (x : CoordinateSpace N) :
    (∀ y, raisedBracket P B x y = 0) ↔ x ∈ B.orthogonal (support P) := by
  constructor
  · intro hx
    have hs : support P ≤ LinearMap.ker (B x) := by
      rw [← bracket_span_eq_support P B hB]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨a, b⟩, rfl⟩
      change B x (raisedBracket P B a b) = 0
      rw [← raisedBracket_invariant P B hsym, hx]
      simp
    intro w hw
    rw [hsym.eq]
    exact hs hw
  · intro hx y
    apply hB.1
    intro z
    rw [raisedBracket_invariant P B hsym]
    rw [hsym.eq]
    apply hx
    apply Submodule.subset_span
    exact ⟨(B y, B z), rfl⟩

/-- Choose a compatible metric nondegenerate both globally and on the support. -/
theorem exists_support_metric (P : Trivector N)
    (hfree : ∀ v : CoordinateSpace N, v ≠ 0 →
      ∃ H ∈ compatibleForms P, H v v ≠ 0) :
    ∃ B ∈ compatibleForms P, B.Nondegenerate ∧ (B.restrict (support P)).Nondegenerate :=
  NondegenerateForm.exists_nondegenerate_and_restrict (compatibleForms P)
    (compatibleForms_isSymm P) hfree (support P)

/-- Contraction always lands in its support, so the metric bracket restricts. -/
def restrictedBracket (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) :
    support P →ₗ[ℂ] support P →ₗ[ℂ] support P where
  toFun x := {
    toFun y := ⟨raisedBracket P B x y, Submodule.subset_span ⟨(B x, B y), rfl⟩⟩
    map_add' := by intro y z; apply Subtype.ext; exact (raisedBracket P B x).map_add y z
    map_smul' := by intro c y; apply Subtype.ext; exact (raisedBracket P B x).map_smul c y }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact congrArg (fun f => f (z : CoordinateSpace N)) ((raisedBracket P B).map_add x y)
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    exact congrArg (fun f => f (y : CoordinateSpace N)) ((raisedBracket P B).map_smul c x)

@[simp] theorem restrictedBracket_coe (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (x y : support P) :
    (restrictedBracket P B x y : CoordinateSpace N) = raisedBracket P B x y := rfl

theorem restrictedBracket_self (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (x : support P) :
    restrictedBracket P B x x = 0 := by
  apply Subtype.ext
  exact raisedBracket_self P B x

theorem restrictedBracket_invariant (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (x y z : support P) :
    B.restrict (support P) (restrictedBracket P B x y) z =
      B.restrict (support P) x (restrictedBracket P B y z) :=
  raisedBracket_invariant P B hsym x y z

theorem restrictedBracket_compatible (P : Trivector N)
    (B H : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hH : HessianCompatibility.Compatible P H) :
    SupportLie.Compatible (restrictedBracket P B) (H.restrict (support P)) := by
  intro a b c d
  exact raisedBracket_compatible P B H hH a b c d

@[instance_reducible]
def supportLieRing (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : (B.restrict (support P)).Nondegenerate)
    (hK : HessianCompatibility.Compatible P B) : LieRing (support P) :=
  SupportLie.lieRingOfCompatible (restrictedBracket P B) (B.restrict (support P)) hB
    (restrictedBracket_self P B) (restrictedBracket_invariant P B hsym)
    (restrictedBracket_compatible P B B hK)

@[instance_reducible]
def supportLieAlgebra (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : (B.restrict (support P)).Nondegenerate)
    (hK : HessianCompatibility.Compatible P B) :
    @LieAlgebra ℂ (support P) inferInstance (supportLieRing P B hsym hB hK) :=
  SupportLie.lieAlgebraOfCompatible (restrictedBracket P B) (B.restrict (support P)) hB
    (restrictedBracket_self P B) (restrictedBracket_invariant P B hsym)
    (restrictedBracket_compatible P B B hK)

/-- Modulo the orthogonal (central) complement, every ambient bracket is a
bracket of two support vectors. -/
theorem exists_support_arguments (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (hB : B.Nondegenerate) (hBr : (B.restrict (support P)).Nondegenerate)
    (x y : CoordinateSpace N) :
    ∃ a b : support P, raisedBracket P B x y = raisedBracket P B a b := by
  have hc := B.isCompl_orthogonal_of_restrict_nondegenerate hsym.isRefl hBr
  obtain ⟨a, z, hx, _⟩ := Submodule.existsUnique_add_of_isCompl hc x
  obtain ⟨b, w, hy, _⟩ := Submodule.existsUnique_add_of_isCompl hc y
  have hz := (central_iff_orthogonal_support P B hsym hB z).mpr z.property
  have hw := (central_iff_orthogonal_support P B hsym hB w).mpr w.property
  refine ⟨a, b, ?_⟩
  rw [← hx, ← hy]
  simp only [map_add, LinearMap.add_apply, hz]
  rw [SupportLie.skew_of_alternating (raisedBracket P B) (raisedBracket_self P B) a w,
    hw, neg_zero, add_zero]
  simp

/-- The restricted support bracket is perfect: its values span the support. -/
theorem restricted_bracket_span_eq_top (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (hB : B.Nondegenerate) (hBr : (B.restrict (support P)).Nondegenerate) :
    Submodule.span ℂ (Set.range (fun p : support P × support P =>
      restrictedBracket P B p.1 p.2)) = ⊤ := by
  apply Submodule.map_injective_of_injective (support P).injective_subtype
  rw [Submodule.map_subtype_top, Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    exact (restrictedBracket P B a b).property
  · conv_lhs => rw [← bracket_span_eq_support P B hB]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    obtain ⟨a, b, hab⟩ := exists_support_arguments P B hsym hB hBr x y
    change raisedBracket P B x y ∈ _
    rw [hab]
    apply Submodule.subset_span
    exact ⟨restrictedBracket P B a b, ⟨(a, b), rfl⟩, rfl⟩

/-- The metric on the support has no nonzero central vector. -/
theorem support_center_zero (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (hB : B.Nondegenerate) (hBr : (B.restrict (support P)).Nondegenerate)
    (x : support P) (hx : ∀ y, restrictedBracket P B x y = 0) : x = 0 :=
  SupportLie.eq_zero_of_central_of_bracket_span_eq_top (restrictedBracket P B)
    (B.restrict (support P)) hBr (restrictedBracket_invariant P B hsym)
    (restricted_bracket_span_eq_top P B hsym hB hBr) x hx

/-- The trivector vanishes on any covector annihilating its support. This is
the dual-space characterization of its tensor support. -/
theorem trivector_zero_of_annihilates_support (P : Trivector N) (α β γ : Covector N)
    (hα : ∀ w ∈ support P, α w = 0) : P ![α, β, γ] = 0 := by
  rw [trivector_cyclic P α β γ, ← contraction_eval]
  exact hα _ (Submodule.subset_span ⟨(β, γ), rfl⟩)

theorem contraction_zero_of_annihilates_support (P : Trivector N) (α β : Covector N)
    (hα : ∀ w ∈ support P, α w = 0) : contraction P α β = 0 := by
  ext a
  exact trivector_zero_of_annihilates_support P α β (coordinateCovector a) hα

/-- The contraction depends only on a covector's restriction to the support. -/
theorem contraction_eq_of_agree_on_support (P : Trivector N) (α α' β : Covector N)
    (hα : ∀ w ∈ support P, α w = α' w) : contraction P α β = contraction P α' β := by
  have hz := contraction_zero_of_annihilates_support P (α - α') β
    (fun w hw => by simp only [LinearMap.sub_apply, hα w hw, sub_self])
  simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using hz

/-- Restricted compatible forms remain basepoint-free on the support. -/
theorem restricted_family_basepoint_free (P : Trivector N)
    (hfree : ∀ v : CoordinateSpace N, v ≠ 0 →
      ∃ H ∈ compatibleForms P, H v v ≠ 0) :
    ∀ w : support P, w ≠ 0 →
      ∃ H ∈ compatibleForms P, (H.restrict (support P)) w w ≠ 0 := by
  intro w hw
  have hw' : (w : CoordinateSpace N) ≠ 0 := fun h => hw (Subtype.ext h)
  exact hfree w hw'

/-- The compatible-family relation on the constructed support Lie algebra is
exactly the relation used by the already verified obstruction lemmas L2. -/
theorem restricted_obstruction_compatible (P : Trivector N)
    (B H : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm)
    (hB : (B.restrict (support P)).Nondegenerate)
    (hKB : HessianCompatibility.Compatible P B) (hH : HessianCompatibility.Compatible P H) :
    letI := supportLieRing P B hsym hB hKB
    letI := supportLieAlgebra P B hsym hB hKB
    LieObstruction.Compatible (H.restrict (support P)) := by
  exact restrictedBracket_compatible P B H hH

/-- Nonzero trivectors have nonzero support. -/
theorem support_ne_bot (P : Trivector N) (hP : P ≠ 0) : support P ≠ ⊥ := by
  intro hs
  apply hP
  apply AlternatingMap.ext
  intro α
  change P α = 0
  have hv : α = ![α 0, α 1, α 2] := by
    funext i
    fin_cases i <;> rfl
  have hmem : contraction P (α 0) (α 1) ∈ support P :=
    Submodule.subset_span ⟨(α 0, α 1), rfl⟩
  rw [hs] at hmem
  have hz : contraction P (α 0) (α 1) = 0 := by simpa using hmem
  have he := contraction_eval P (α 0) (α 1) (α 2)
  rw [hz, map_zero] at he
  rw [hv]
  exact he.symm

/-- L1 as a single existence theorem. The compatible metric and both Lie
instances are constructed from basepoint-freeness; none are additional hypotheses. -/
theorem exists_support_lie_data (P : Trivector N)
    (hfree : ∀ v : CoordinateSpace N, v ≠ 0 →
      ∃ H ∈ compatibleForms P, H v v ≠ 0) :
    ∃ (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hmem : B ∈ compatibleForms P)
      (_hB : B.Nondegenerate) (hBr : (B.restrict (support P)).Nondegenerate),
      letI := supportLieRing P B (compatibleForms_isSymm P B hmem) hBr hmem.1
      letI := supportLieAlgebra P B (compatibleForms_isSymm P B hmem) hBr hmem.1
      (∀ x y : support P, ⁅x, y⁆ = restrictedBracket P B x y) ∧
      (∀ x y z : support P, (B.restrict (support P)) ⁅x, y⁆ z =
        (B.restrict (support P)) x ⁅y, z⁆) ∧
      (∀ H ∈ compatibleForms P, LieObstruction.Compatible (H.restrict (support P))) ∧
      LieObstruction.BasepointFree (Set.range (fun H : compatibleForms P =>
        H.val.restrict (support P))) ∧
      Submodule.span ℂ (Set.range (fun p : support P × support P => ⁅p.1, p.2⁆)) = ⊤ ∧
      (∀ x : support P, (∀ y : support P, ⁅x, y⁆ = 0) → x = 0) := by
  obtain ⟨B, hmem, hB, hBr⟩ := exists_support_metric P hfree
  refine ⟨B, hmem, hB, hBr, ?_⟩
  refine ⟨fun _ _ => rfl, restrictedBracket_invariant P B (compatibleForms_isSymm P B hmem),
    ?_, ?_, restricted_bracket_span_eq_top P B (compatibleForms_isSymm P B hmem) hB hBr,
    support_center_zero P B (compatibleForms_isSymm P B hmem) hB hBr⟩
  · intro H hH
    exact restricted_obstruction_compatible P B H (compatibleForms_isSymm P B hmem) hBr hmem.1 hH.1
  · intro w hw
    obtain ⟨H, hH, hHw⟩ := restricted_family_basepoint_free P hfree w hw
    exact ⟨H.restrict (support P), ⟨⟨H, hH⟩, rfl⟩, hHw⟩

end NcCubic.SupportConstruction
