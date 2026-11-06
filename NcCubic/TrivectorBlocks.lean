module
public import NcCubic.SupportConstruction
public import NcCubic.ExteriorComparison
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FinCases

@[expose] public section
noncomputable section
namespace NcCubic.TrivectorBlocks
open scoped BigOperators

/-- A trilinear Cartan form splits along orthogonal commuting factors and a
central complement. All factor conditions are explicit here. -/
theorem trilinear_block_decomposition
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι]
    (T : V →ₗ[F] V →ₗ[F] V →ₗ[F] F) (p : ι → V →ₗ[F] V) (Z : V →ₗ[F] V)
    (hsum : ∀ x : V, (∑ s, p s x) + Z x = x)
    (hz₁ : ∀ x y z, T (Z x) y z = 0)
    (hz₂ : ∀ x y z, T x (Z y) z = 0)
    (hz₃ : ∀ x y z, T x y (Z z) = 0)
    (hmixed : ∀ s t u, s ≠ t ∨ s ≠ u →
      ∀ x y z, T (p s x) (p t y) (p u z) = 0)
    (x y z : V) : T x y z = ∑ s, T (p s x) (p s y) (p s z) := by
  have he : T x y z = T ((∑ s, p s x) + Z x)
      ((∑ s, p s y) + Z y) ((∑ s, p s z) + Z z) := by
    rw [hsum, hsum, hsum]
  rw [he]
  simp only [map_add, map_sum, LinearMap.add_apply, LinearMap.sum_apply,
    hz₁, hz₂, hz₃, add_zero, Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro s hs
  have ht (t : ι) : (∑ u, T (p u x) (p t y) (p s z)) =
      if s = t then T (p s x) (p s y) (p s z) else 0 := by
    by_cases h : s = t
    · subst t
      rw [ite_eq_left rfl]
      apply Finset.sum_eq_single s
      · intro u _ hu
        exact hmixed u s s (Or.inr hu) x y z
      · simp
    · rw [ite_eq_right h]
      apply Finset.sum_eq_zero
      intro u _
      by_cases hu : u = s
      · subst u; exact hmixed s t s (Or.inl h) x y z
      · exact hmixed u t s (Or.inr hu) x y z
  simp_rw [ht]
  simp

/-- Every alternating three-form on a three-dimensional coordinate space is
its value on the standard basis times the determinant. -/
theorem three_form_eq_det
    (T : AlternatingMap ℂ (CoordinateSpace 3) ℂ (Fin 3))
    (v : Fin 3 → CoordinateSpace 3) :
    T v = T (Pi.basisFun ℂ (Fin 3)) * Matrix.det (fun i j => v i j) := by
  have h := T.eq_smul_basis_det (Pi.basisFun ℂ (Fin 3))
  have he := congrArg (fun Q : AlternatingMap ℂ (CoordinateSpace 3) ℂ (Fin 3) => Q v) h
  simpa [Module.Basis.det_apply, Module.Basis.toMatrix, Matrix.det_transpose, Matrix.det] using he

/-- The Cartan pairing as a curried trilinear map. -/
def cartanTrilinear {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (C : V →ₗ[F] V →ₗ[F] V) (B : LinearMap.BilinForm F V) :
    V →ₗ[F] V →ₗ[F] V →ₗ[F] F where
  toFun x := LinearMap.comp B (C x)
  map_add' := by intro x y; ext z w; simp
  map_smul' := by intro c x; ext y z; simp

/-- Commuting factor projections and a central complement split the Cartan
three-form. These are the precise conditional factor hypotheses of this helper. -/
theorem cartan_block_decomposition
    {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq ι]
    (C : V →ₗ[F] V →ₗ[F] V) (B : LinearMap.BilinForm F V)
    (hself : ∀ x, C x x = 0)
    (hinv : ∀ x y z, B (C x y) z = B x (C y z))
    (p : ι → V →ₗ[F] V) (Z : V →ₗ[F] V)
    (hsum : ∀ x : V, (∑ s, p s x) + Z x = x)
    (hcenter : ∀ x y, C (Z x) y = 0)
    (hcomm : ∀ s t, s ≠ t → ∀ x y, C (p s x) (p t y) = 0)
    (x y z : V) :
    B (C x y) z = ∑ s, B (C (p s x) (p s y)) (p s z) := by
  apply trilinear_block_decomposition (cartanTrilinear C B) p Z hsum
  · intro a b c
    change B (C (Z a) b) c = 0
    simp [hcenter]
  · intro a b c
    change B (C a (Z b)) c = 0
    rw [SupportLie.skew_of_alternating C hself a (Z b), hcenter]
    simp
  · intro a b c
    change B (C a b) (Z c) = 0
    rw [hinv, SupportLie.skew_of_alternating C hself b (Z c), hcenter]
    simp
  · intro s t u h a b c
    change B (C (p s a) (p t b)) (p u c) = 0
    by_cases hst : s = t
    · subst t
      have hsu : s ≠ u := h.resolve_left (not_not_intro rfl)
      rw [hinv, hcomm s u hsu]
      simp
    · rw [hcomm s t hst]
      simp

/-- Scale only the first vector of each active triple. -/
def volumeScale {k m : ℕ} (c : Fin k → ℂ) : BlockIndex k m → ℂ :=
  Sum.elim (fun si => if si.2 = 0 then c si.1 else 1) (fun _ => 1)

theorem volumeScale_isUnit {k m : ℕ} (c : Fin k → ℂ) (hc : ∀ s, c s ≠ 0)
    (i : BlockIndex k m) : IsUnit (volumeScale c i) := by
  cases i with
  | inl si =>
    by_cases h : si.2 = 0
    · simpa [volumeScale, h] using (isUnit_iff_ne_zero.mpr (hc si.1))
    · simp [volumeScale, h]
  | inr j => simp [volumeScale]

/-- A nonzero scalar on each volume block is removed by changing one basis
vector per block. No extraction of cube roots is involved. -/
theorem normalize_volume_blocks {N k m : ℕ} (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (c : Fin k → ℂ) (hc : ∀ s, c s ≠ 0)
    (hP : ∀ α : Fin 3 → Covector N,
      P α = ∑ s : Fin k, c s * Matrix.det (fun i j : Fin 3 => α i (b (Sum.inl (s, j))))) :
    ∃ b' : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N), HasBlockTrivector P b' := by
  classical
  let hw : ∀ i : BlockIndex k m, IsUnit (volumeScale c i) := volumeScale_isUnit c hc
  refine ⟨b.isUnitSMul hw, ?_⟩
  intro α
  rw [hP]
  apply Finset.sum_congr rfl
  intro s hs
  let M : Matrix (Fin 3) (Fin 3) ℂ := fun i j => α i (b (Sum.inl (s, j)))
  have hm : (fun i j : Fin 3 => α i ((b.isUnitSMul hw) (Sum.inl (s, j)))) =
      M.updateCol 0 (c s • fun i => M i 0) := by
    ext i j
    rw [Module.Basis.isUnitSMul_apply]
    by_cases h : j = 0
    · subst j
      simp [volumeScale, Matrix.updateCol, Function.update, M]
    · simp [volumeScale, h, Matrix.updateCol, Function.update, M]
  rw [hm, Matrix.det_updateCol_smul, Matrix.updateCol_eq_self]

/-- Include the coordinate space of a proposed three-dimensional factor. -/
def factorInclusion {N k : ℕ} (v : Fin k → Fin 3 → CoordinateSpace N) (s : Fin k) :
    CoordinateSpace 3 →ₗ[ℂ] CoordinateSpace N :=
  (Pi.basisFun ℂ (Fin 3)).constr ℂ (v s)

theorem factorInclusion_apply {N k : ℕ} (v : Fin k → Fin 3 → CoordinateSpace N)
    (s : Fin k) (x : CoordinateSpace 3) :
    factorInclusion v s x = ∑ j : Fin 3, x j • v s j := by
  simp [factorInclusion, Module.Basis.constr_apply_fintype]

/-- The alternating Cartan three-form on the coordinates of a proposed factor. -/
def factorThreeForm {N k : ℕ} (P : Trivector N)
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (v : Fin k → Fin 3 → CoordinateSpace N) (s : Fin k) :
    AlternatingMap ℂ (CoordinateSpace 3) ℂ (Fin 3) :=
  P.compLinearMap (LinearMap.comp B (factorInclusion v s))

/-- The weighted volume reconstruction, conditional on explicit commuting
factor projections and their metric-dual coordinate description. This does not
assume the desired equality of tensors as a hypothesis. -/
theorem weighted_volume_of_commuting_factors {N k m : ℕ}
    (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (v : Fin k → Fin 3 → CoordinateSpace N)
    (p : Fin k → CoordinateSpace N →ₗ[ℂ] CoordinateSpace N)
    (Z : CoordinateSpace N →ₗ[ℂ] CoordinateSpace N)
    (hsum : ∀ x, (∑ s, p s x) + Z x = x)
    (hcenter : ∀ x y, SupportConstruction.raisedBracket P B (Z x) y = 0)
    (hcomm : ∀ s t, s ≠ t → ∀ x y,
      SupportConstruction.raisedBracket P B (p s x) (p t y) = 0)
    (hproj : ∀ (s : Fin k) (α : Covector N),
      p s ((B.toDual hB).symm α) =
        ∑ j : Fin 3, α (b (Sum.inl (s, j))) • v s j)
    (α : Fin 3 → Covector N) :
    P α = ∑ s : Fin k, factorThreeForm P B v s (Pi.basisFun ℂ (Fin 3)) *
      Matrix.det (fun i j : Fin 3 => α i (b (Sum.inl (s, j)))) := by
  let x : Fin 3 → CoordinateSpace N := fun i => (B.toDual hB).symm (α i)
  have hx (i : Fin 3) : B (x i) = α i := (B.toDual hB).apply_symm_apply (α i)
  have hα : P α = B (SupportConstruction.raisedBracket P B (x 0) (x 1)) (x 2) := by
    rw [SupportConstruction.pair_raisedBracket P B hsym, hx, hx, hx]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hα, cartan_block_decomposition (SupportConstruction.raisedBracket P B) B
    (SupportConstruction.raisedBracket_self P B)
    (SupportConstruction.raisedBracket_invariant P B hsym) p Z hsum hcenter hcomm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [SupportConstruction.pair_raisedBracket P B hsym]
  let a : Fin 3 → CoordinateSpace 3 := fun i j => α i (b (Sum.inl (s, j)))
  have ha : P ![B (p s (x 0)), B (p s (x 1)), B (p s (x 2))] =
      factorThreeForm P B v s a := by
    change P ![B (p s (x 0)), B (p s (x 1)), B (p s (x 2))] =
      P (fun i => B (factorInclusion v s (a i)))
    congr 1
    funext i
    fin_cases i <;> simp [factorInclusion_apply, a, x, hproj]
  rw [ha, three_form_eq_det]

/-- Conditional L5 reconstruction from explicit factor and metric-dual
projection data, with each local Cartan three-form nonzero. -/
theorem normal_form_of_commuting_three_factors {N k m : ℕ}
    (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (v : Fin k → Fin 3 → CoordinateSpace N)
    (p : Fin k → CoordinateSpace N →ₗ[ℂ] CoordinateSpace N)
    (Z : CoordinateSpace N →ₗ[ℂ] CoordinateSpace N)
    (hsum : ∀ x, (∑ s, p s x) + Z x = x)
    (hcenter : ∀ x y, SupportConstruction.raisedBracket P B (Z x) y = 0)
    (hcomm : ∀ s t, s ≠ t → ∀ x y,
      SupportConstruction.raisedBracket P B (p s x) (p t y) = 0)
    (hproj : ∀ (s : Fin k) (α : Covector N),
      p s ((B.toDual hB).symm α) =
        ∑ j : Fin 3, α (b (Sum.inl (s, j))) • v s j)
    (hnonzero : ∀ s, factorThreeForm P B v s ≠ 0) :
    ∃ b' : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N), HasBlockTrivector P b' := by
  apply normalize_volume_blocks P b (fun s => factorThreeForm P B v s (Pi.basisFun ℂ (Fin 3)))
  · intro s hz
    apply hnonzero s
    exact (AlternatingMap.map_basis_eq_zero_iff (Pi.basisFun ℂ (Fin 3))
      (factorThreeForm P B v s)).mp hz
  · exact weighted_volume_of_commuting_factors P B hsym hB b v p Z hsum hcenter hcomm hproj

end NcCubic.TrivectorBlocks
