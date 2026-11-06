module
public import NcCubic.GradientSyzygy
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.GradedKoszul
open MvPolynomial

/-- The component in the degree of a homogeneous factor sees only the
constant coefficient of its multiplier. -/
theorem homogeneousComponent_mul_same_degree {K σ : Type*} [CommRing K]
    {n : ℕ} {g : MvPolynomial σ K} (hg : g.IsHomogeneous n) (p : MvPolynomial σ K) :
    homogeneousComponent n (p * g) = C (p.coeff 0) * g := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_C_mul]
  by_cases hd : d.degree = n
  · rw [ite_eq_left hd, coeff_mul]
    apply Finset.sum_eq_single (0,d)
    · intro x hx hne
      have hxsum := Finset.mem_antidiagonal.mp hx
      by_cases hxdeg : x.2.degree = n
      · have hzdeg : x.1.degree = 0 := by
          have he := congrArg Finsupp.degree hxsum
          simp only [map_add] at he
          omega
        have hz : x.1 = 0 := (Finsupp.degree_eq_zero_iff _).mp hzdeg
        have hx2 : x.2 = d := by simpa [hz] using hxsum
        exact False.elim (hne (Prod.ext hz hx2))
      · rw [hg.coeff_eq_zero hxdeg, mul_zero]
    · intro hn
      exact False.elim (hn (Finset.mem_antidiagonal.mpr (zero_add d)))
  · rw [ite_eq_right hd, hg.coeff_eq_zero hd, mul_zero]

/-- A homogeneous matrix of degree n maps onto its degree-n image already
using constant coefficients. This extracts the constant graded Koszul lift. -/
theorem constant_preimage_of_homogeneous_matrix
    {K σ ι κ M V : Type*} [CommRing K] [Fintype ι] [Fintype κ]
    [AddCommGroup M] [Module (MvPolynomial σ K) M]
    [AddCommGroup V] [Module (MvPolynomial σ K) V]
    (b : Module.Basis ι (MvPolynomial σ K) M)
    (c : Module.Basis κ (MvPolynomial σ K) V)
    (D : M →ₗ[MvPolynomial σ K] V) (n : ℕ)
    (hD : ∀ i j, (c.repr (D (b j)) i).IsHomogeneous n)
    (x : V) (hx : ∀ i, (c.repr x i).IsHomogeneous n)
    (y : M) (hy : D y = x) :
    ∃ a : ι → K, D (∑ j, (C (a j) : MvPolynomial σ K) • b j) = x := by
  classical
  refine ⟨fun j => (b.repr y j).coeff 0, ?_⟩
  apply c.ext_elem
  intro i
  have he : (∑ j, b.repr y j * c.repr (D (b j)) i) = c.repr x i := by
    calc
      _ = c.repr (D (∑ j, b.repr y j • b j)) i := by
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
      _ = _ := by rw [b.sum_repr, hy]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  calc
    _ = ∑ j, homogeneousComponent n (b.repr y j * c.repr (D (b j)) i) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (homogeneousComponent_mul_same_degree (hD i j) (b.repr y j)).symm
    _ = homogeneousComponent n (∑ j, b.repr y j * c.repr (D (b j)) i) := by
      rw [map_sum]
    _ = c.repr x i := by rw [he, homogeneousComponent_eq_self (hx i)]

/-- An image under a positive-degree homogeneous matrix cannot be a nonzero
constant vector. This supplies injectivity of the constant Koszul strand. -/
theorem constant_image_eq_zero_of_positive_degree
    {K σ ι κ M V : Type*} [CommRing K] [Fintype ι] [Fintype κ]
    [AddCommGroup M] [Module (MvPolynomial σ K) M]
    [AddCommGroup V] [Module (MvPolynomial σ K) V]
    (b : Module.Basis ι (MvPolynomial σ K) M)
    (c : Module.Basis κ (MvPolynomial σ K) V)
    (D : M →ₗ[MvPolynomial σ K] V) (n : ℕ) (hn : 0 < n)
    (hD : ∀ i j, (c.repr (D (b j)) i).IsHomogeneous n)
    (x : V) (hx : ∀ i, (c.repr x i).IsHomogeneous 0)
    (y : M) (hy : D y = x) : x = 0 := by
  classical
  apply c.ext_elem
  intro i
  have he : (∑ j, b.repr y j * c.repr (D (b j)) i) = c.repr x i := by
    calc
      _ = c.repr (D (∑ j, b.repr y j • b j)) i := by
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
      _ = _ := by rw [b.sum_repr, hy]
  have hc : (c.repr x i).coeff 0 = 0 := by
    rw [← he, coeff_sum]
    apply Finset.sum_eq_zero
    intro j _
    exact GradientSyzygy.coeff_mul_eq_zero_of_degree_lt (hD i j) _ _ (by simpa)
  have hz : c.repr x i = 0 := by
    rw [← homogeneousComponent_eq_self (hx i), homogeneousComponent_zero, hc, map_zero]
  simpa using hz

end NcCubic.Geometry.GradedKoszul
