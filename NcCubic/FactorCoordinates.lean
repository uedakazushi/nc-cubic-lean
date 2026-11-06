module
public import NcCubic.TrivectorBlocks
@[expose] public section
noncomputable section
namespace NcCubic.TrivectorBlocks
open scoped BigOperators

/-- Coordinate projection onto an active three-dimensional basis block. -/
def blockProjection {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (s : Fin k) :
    CoordinateSpace N →ₗ[ℂ] CoordinateSpace N :=
  ∑ j : Fin 3, (b.coord (Sum.inl (s, j))).smulRight (b (Sum.inl (s, j)))

/-- Projection onto the complementary central basis block. -/
def centerProjection {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) :
    CoordinateSpace N →ₗ[ℂ] CoordinateSpace N :=
  ∑ j : Fin m, (b.coord (Sum.inr j)).smulRight (b (Sum.inr j))

@[simp] theorem blockProjection_apply {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (s : Fin k) (x : CoordinateSpace N) :
    blockProjection b s x = ∑ j : Fin 3, b.repr x (Sum.inl (s, j)) • b (Sum.inl (s, j)) := by
  simp [blockProjection]

@[simp] theorem centerProjection_apply {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (x : CoordinateSpace N) :
    centerProjection b x = ∑ j : Fin m, b.repr x (Sum.inr j) • b (Sum.inr j) := by
  simp [centerProjection]

theorem blockProjection_sum {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (x : CoordinateSpace N) :
    (∑ s : Fin k, blockProjection b s x) + centerProjection b x = x := by
  simpa only [blockProjection_apply, centerProjection_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type] using b.sum_repr x

/-- Coordinates of the metric-inverse covector are evaluations on the metric-dual basis. -/
theorem inverse_metric_coordinates {N k m : ℕ}
    (B : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hsym : B.IsSymm) (hB : B.Nondegenerate)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) (α : Covector N) (i : BlockIndex k m) :
    b.repr ((B.toDual hB).symm α) i = α (B.dualBasis hB b i) := by
  have he (x : CoordinateSpace N) : B (B.dualBasis hB b i) x = b.repr x i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, smul_eq_mul, B.apply_dualBasis_left]
    simp
  rw [← he]
  rw [hsym.eq]
  exact B.apply_toDual_symm_apply α _

/-- A basis whose active triples commute and whose complementary vectors are
central already supplies all projection data needed by volume reconstruction. -/
theorem normal_form_of_commuting_basis {N k m : ℕ}
    (P : Trivector N) (B : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (hsym : B.IsSymm) (hB : B.Nondegenerate)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hcenter : ∀ (j : Fin m) (y : CoordinateSpace N),
      SupportConstruction.raisedBracket P B (b (Sum.inr j)) y = 0)
    (hcomm : ∀ (s t : Fin k), s ≠ t → ∀ i j : Fin 3,
      SupportConstruction.raisedBracket P B (b (Sum.inl (s, i))) (b (Sum.inl (t, j))) = 0)
    (hnonzero : ∀ s, factorThreeForm P B (fun s j => b (Sum.inl (s, j))) s ≠ 0) :
    ∃ b' : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N), HasBlockTrivector P b' := by
  apply normal_form_of_commuting_three_factors P B hsym hB (B.dualBasis hB b)
    (fun s j => b (Sum.inl (s, j))) (blockProjection b) (centerProjection b)
    (blockProjection_sum b)
  · intro x y
    simp [centerProjection_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, hcenter]
  · intro s t hst x y
    simp [blockProjection_apply, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, hcomm s t hst]
  · intro s α
    rw [blockProjection_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [inverse_metric_coordinates B hsym hB]
  · exact hnonzero

end NcCubic.TrivectorBlocks
