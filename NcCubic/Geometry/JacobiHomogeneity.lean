/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.LocalChartHamiltonian
public import NcCubic.Divergence
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}
/-- The genuine coordinate Jacobiator of a homogeneous quadratic bracket is
homogeneous cubic, as required by the projective trivector restriction sequence. -/
theorem jacobiArray_isHomogeneous (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (i j k : Fin N) :
    (jacobiArray q i j k).IsHomogeneous 3 := by
  apply IsHomogeneous.sum
  intro r _
  exact (((hq i r).mul ((hq j k).pderiv (i := r))).add
    ((hq j r).mul ((hq k i).pderiv (i := r)))).add
    ((hq k r).mul ((hq i j).pderiv (i := r)))

theorem jacobiArray_swap_first (q : Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ i j, q j i = -q i j) (i j k : Fin N) :
    jacobiArray q j i k = -jacobiArray q i j k := by
  simp only [jacobiArray, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [hs i k, hs j i, hs k j]
  simp only [map_neg]
  ring

theorem jacobiArray_cyclic (q : Fin N → Fin N → CubicPolynomial N) (i j k : Fin N) :
    jacobiArray q j k i = jacobiArray q i j k := by
  simp only [jacobiArray]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem jacobiArray_swap_last (q : Fin N → Fin N → CubicPolynomial N)
    (hs : ∀ i j, q j i = -q i j) (i j k : Fin N) :
    jacobiArray q i k j = -jacobiArray q i j k := by
  rw [← jacobiArray_cyclic q i k j, jacobiArray_swap_first q hs j k i,
    jacobiArray_cyclic q i j k]

/-- The Jacobiator used in the geometric lift has actual cubic coefficients. -/
theorem contraction_jacobiArray_isHomogeneous (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (i j k : Fin N) :
    (jacobiArray (contractionCoefficients F P) i j k).IsHomogeneous 3 :=
  jacobiArray_isHomogeneous _ (contractionCoefficients_isHomogeneous F P hF) i j k
end NcCubic.Geometry
