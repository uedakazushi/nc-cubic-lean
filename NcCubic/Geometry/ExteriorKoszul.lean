/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local graded Koszul bridge; upstream dependency licenses are preserved.
-/
module
public import NcCubic.Geometry.GradedKoszul
public import NcCubic.Geometry.HomogeneousProjection
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.GradedKoszul
open MvPolynomial
open scoped BigOperators

theorem koszul_d_ιMulti {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : Module.Dual R M) (n : ℕ) (v : Fin (n + 1) → M) :
    Koszul.d φ n (exteriorPower.ιMulti R (n + 1) v) =
      ∑ k : Fin (n + 1), ((-1 : R) ^ k.val * φ (v k)) •
        exteriorPower.ιMulti R n (v ∘ k.succAbove) := by
  apply Subtype.ext
  simp only [Koszul.d_apply_coe, exteriorPower.ιMulti_apply_coe,
    Submodule.coe_sum, Submodule.coe_smul]
  exact Koszul.contraction_ιMulti φ n v

/-- Standard wedge vectors have constant coordinates in the exterior basis. -/
theorem exterior_basis_coordinate_constant {K σ I M : Type*} [CommRing K]
    [LinearOrder I] [AddCommGroup M] [Module (MvPolynomial σ K) M]
    (b : Module.Basis I (MvPolynomial σ K) M) (n : ℕ)
    (v : Fin n → I) (s : Set.powersetCard I n) :
    ∃ c : K, (b.exteriorPower n).repr
      (exteriorPower.ιMulti (MvPolynomial σ K) n (fun k => b (v k))) s = C c := by
  classical
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self]
  let A : Matrix (Fin n) (Fin n) K := fun i j =>
    if v i = Set.powersetCard.ofFinEmbEquiv.symm s j then 1 else 0
  refine ⟨A.det, ?_⟩
  rw [RingHom.map_det C]
  apply congrArg Matrix.det
  funext i j
  change (Finsupp.single (v i) (1 : MvPolynomial σ K))
    (Set.powersetCard.ofFinEmbEquiv.symm s j) = C (A i j)
  simp only [A, Finsupp.single_apply]
  split_ifs <;> simp_all

end NcCubic.Geometry.GradedKoszul

namespace NcCubic.Geometry.GradedKoszul
open MvPolynomial
open scoped BigOperators

/-- The matrix of Koszul contraction has the degree of the functional's
values on the original basis. -/
theorem koszul_matrix_homogeneous {K σ I M : Type*} [CommRing K]
    [LinearOrder I] [AddCommGroup M] [Module (MvPolynomial σ K) M]
    (b : Module.Basis I (MvPolynomial σ K) M)
    (φ : Module.Dual (MvPolynomial σ K) M) (d n : ℕ)
    (hφ : ∀ j, (φ (b j)).IsHomogeneous d)
    (i : Set.powersetCard I n) (j : Set.powersetCard I (n + 1)) :
    ((b.exteriorPower n).repr (Koszul.d φ n (b.exteriorPower (n + 1) j)) i).IsHomogeneous d := by
  classical
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  rw [koszul_d_ιMulti]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply IsHomogeneous.sum
  intro k _
  obtain ⟨c, hc⟩ := exterior_basis_coordinate_constant b n
    (fun l => Set.powersetCard.ofFinEmbEquiv.symm j (k.succAbove l)) i
  change (((-1 : MvPolynomial σ K) ^ k.val *
    φ (b (Set.powersetCard.ofFinEmbEquiv.symm j k))) *
      (b.exteriorPower n).repr (exteriorPower.ιMulti (MvPolynomial σ K) n
        (fun l => b (Set.powersetCard.ofFinEmbEquiv.symm j (k.succAbove l)))) i).IsHomogeneous d
  rw [hc]
  convert (hφ (Set.powersetCard.ofFinEmbEquiv.symm j k)).C_mul ((-1 : K)^k.val * c) using 1
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

end NcCubic.Geometry.GradedKoszul

namespace NcCubic.Geometry.GradedKoszul
open MvPolynomial
open scoped BigOperators

/-- Exactness of the required graded strand: every degree-two polynomial
bivector killed by dF is the contraction of a constant trivector. -/
theorem quadratic_bivector_constant_boundary {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (F : MvPolynomial (Fin N) K) (hF : F.IsHomogeneous 3)
    (hiso : ∀ x : Fin N → K, (∀ i, eval x (pderiv i F) = 0) → x = 0)
    (q : ⋀[MvPolynomial (Fin N) K]^2 (Fin N → MvPolynomial (Fin N) K))
    (hdegree : ∀ i, (((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 2).repr q i).IsHomogeneous 2)
    (hcycle : Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 1 q = 0) :
    ∃ a : Set.powersetCard (Fin N) 3 → K,
      Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 2
        (∑ j, (C (a j) : MvPolynomial (Fin N) K) •
          (Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3 j) = q := by
  classical
  obtain ⟨y, hy⟩ := gradient_cycle_is_boundary F hF hiso 1 q hcycle
  apply constant_preimage_of_homogeneous_matrix
    ((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3)
    ((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 2)
    (Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 2) 2 _ q hdegree y hy
  intro i j
  apply koszul_matrix_homogeneous
  intro a
  simpa only [Pi.basisFun_apply, Koszul.seqDual_single] using hF.pderiv (i := a)

end NcCubic.Geometry.GradedKoszul

namespace NcCubic.Geometry.GradedKoszul
open MvPolynomial
open scoped BigOperators

/-- Injectivity of the constant trivector strand of the actual gradient
Koszul complex, proved from higher exactness and the positive grading. -/
theorem constant_trivector_cycle_zero {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (F : MvPolynomial (Fin N) K) (hF : F.IsHomogeneous 3)
    (hiso : ∀ x : Fin N → K, (∀ i, eval x (pderiv i F) = 0) → x = 0)
    (z : ⋀[MvPolynomial (Fin N) K]^3 (Fin N → MvPolynomial (Fin N) K))
    (hdegree : ∀ i, (((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3).repr z i).IsHomogeneous 0)
    (hcycle : Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 2 z = 0) : z = 0 := by
  classical
  obtain ⟨y, hy⟩ := gradient_cycle_is_boundary F hF hiso 2 z hcycle
  apply constant_image_eq_zero_of_positive_degree
    ((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 4)
    ((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3)
    (Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 3) 2 (by decide) _ z hdegree y hy
  intro i j
  apply koszul_matrix_homogeneous
  intro a
  simpa only [Pi.basisFun_apply, Koszul.seqDual_single] using hF.pderiv (i := a)

/-- The graded segment S₀⊗Λ³ → S₂⊗Λ² → S₄⊗V is exact, with unique
constant preimage in its first term. -/
theorem quadratic_bivector_unique_constant_boundary {K : Type*} [Field K] [IsAlgClosed K] {N : ℕ}
    (F : MvPolynomial (Fin N) K) (hF : F.IsHomogeneous 3)
    (hiso : ∀ x : Fin N → K, (∀ i, eval x (pderiv i F) = 0) → x = 0)
    (q : ⋀[MvPolynomial (Fin N) K]^2 (Fin N → MvPolynomial (Fin N) K))
    (hdegree : ∀ i, (((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 2).repr q i).IsHomogeneous 2)
    (hcycle : Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 1 q = 0) :
    ∃! z : ⋀[MvPolynomial (Fin N) K]^3 (Fin N → MvPolynomial (Fin N) K),
      (∀ i, (((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3).repr z i).IsHomogeneous 0) ∧
      Koszul.d (Koszul.seqDual (fun i => pderiv i F)) 2 z = q := by
  classical
  obtain ⟨a, ha⟩ := quadratic_bivector_constant_boundary F hF hiso q hdegree hcycle
  let z := ∑ j, (C (a j) : MvPolynomial (Fin N) K) •
    (Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3 j
  have hzdegree : ∀ i, (((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3).repr z i).IsHomogeneous 0 := by
    intro i
    have he : (((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3).repr z i) = C (a i) := by
      change (((Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3).repr
        (∑ j, (C (a j) : MvPolynomial (Fin N) K) •
          (Pi.basisFun (MvPolynomial (Fin N) K) (Fin N)).exteriorPower 3 j) i) = C (a i)
      simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
      simp
    rw [he]
    exact isHomogeneous_C (Fin N) (a i)
  refine ⟨z, ⟨hzdegree, ha⟩, ?_⟩
  intro w hw
  apply sub_eq_zero.mp
  apply constant_trivector_cycle_zero F hF hiso (w - z)
  · intro i
    simpa only [map_sub, Finsupp.sub_apply] using (hw.1 i).sub (hzdegree i)
  · rw [map_sub, hw.2, ha, sub_self]

end NcCubic.Geometry.GradedKoszul
