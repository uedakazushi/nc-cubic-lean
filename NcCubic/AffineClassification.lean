/- Assembly of the affine classification, with its full original contract. -/
module
public import NcCubic.CubicJacobi
public import NcCubic.BlockHessian
public import NcCubic.BlockContraction
public import NcCubic.BlockClassification

@[expose] public section
noncomputable section
namespace NcCubic

/-- A block-indexed coordinate basis gives the expected ambient dimension. -/
theorem block_basis_dimension {N k m : ℕ}
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) : N = 3*k+m := by
  have hb := Module.finrank_eq_card_basis b
  simpa [CoordinateSpace, BlockIndex, Nat.mul_comm] using hb

/-- A nonzero tensor cannot have an empty volume-block presentation. -/
theorem block_count_positive {N k m : ℕ} (P : Trivector N) (hP : P ≠ 0)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
    (hb : HasBlockTrivector P b) : 1 ≤ k := by
  by_contra hn
  have hk : k = 0 := by omega
  subst k
  apply hP
  apply AlternatingMap.ext
  intro α
  change P α = 0
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hb α

/-- The complete coordinate-level classification, with the hypotheses in the
original project contract. The projective representation/lifting theorem is
still a separate obligation and is not asserted here. -/
theorem theorem113_affine : AffineClassificationStatement := by
  intro N _hN F P _hFne hF hgrad hP
  constructor
  · intro hJ
    have hH := (CubicJacobi.jacobi_iff_hessians_compatible F P hF hgrad).1 hJ
    have hfree := CubicJacobi.compatibleForms_basepoint_free_of_jacobi F P hF hgrad hJ
    obtain ⟨k,m,b,hb⟩ := TrivectorBlocks.has_block_trivector_of_basepoint_free P hfree
    exact BlockHessian.hasBlockNormalForm_of_compatible hF P
      (block_count_positive P hP b hb) (block_basis_dimension b) b hb hH
  · exact normalForm_satisfiesJacobi F P

end NcCubic
