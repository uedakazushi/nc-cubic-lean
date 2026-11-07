/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.HomogeneousBasicBracket
public import NcCubic.Divergence
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}
variable (S : Submonoid (CubicPolynomial N)) (L : Type*) [CommRing L]
  [Algebra (CubicPolynomial N) L] [IsLocalization S L] [Algebra ℂ L]
  [IsScalarTower ℂ (CubicPolynomial N) L]
/-- The genuine Euler derivation on the localized polynomial ring. -/
def localizedEuler : Derivation ℂ L L :=
  ∑ i, algebraMap (CubicPolynomial N) L (X i) • LocalizedPoisson.localizedPderiv S L i

@[simp] theorem localizedEuler_algebraMap (a : CubicPolynomial N) :
    localizedEuler S L (algebraMap _ L a) =
      algebraMap _ L (∑ i, X i * pderiv i a) := by
  simp [localizedEuler, LocalizedPoisson.localizedPderiv, Algebra.smul_def]

theorem localizedEuler_homogeneous (a : CubicPolynomial N) {d : ℕ}
    (ha : a.IsHomogeneous d) :
    localizedEuler S L (algebraMap _ L a) = (d : L) * algebraMap _ L a := by
  rw [localizedEuler_algebraMap, ha.sum_X_mul_pderiv]
  simp [nsmul_eq_mul]

/-- Degree-zero homogeneous functions are annihilated by the genuine Euler
field, on every homogeneous basic open. -/
theorem localizedEuler_degreeZero {h : CubicPolynomial N} {d : ℕ} (hh : h.IsHomogeneous d)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    localizedEuler (Submonoid.powers h) (Localization.Away h) x.val = 0 := by
  obtain ⟨n,a,hn,ha,hx⟩ := HomogeneousBasic.exists_positive_rep hh x
  let D := localizedEuler (Submonoid.powers h) (Localization.Away h)
  let t := algebraMap (CubicPolynomial N) (Localization.Away h) h
  have ht : D (t^n) = (n*d : ℕ) * t^n := by
    change localizedEuler (Submonoid.powers h) (Localization.Away h)
      ((algebraMap (CubicPolynomial N) (Localization.Away h) h)^n) = _
    rw [← map_pow]
    simpa only [map_pow, Nat.mul_comm] using
      localizedEuler_homogeneous (Submonoid.powers h) (Localization.Away h) (h^n) (hh.pow n)
  have hd := congrArg D hx
  rw [Derivation.leibniz, ht] at hd
  change t^n * D x.val + x.val * ((n*d : ℕ) * t^n) =
    D (algebraMap _ _ a) at hd
  rw [localizedEuler_homogeneous _ _ a ha] at hd
  have hz : t^n * D x.val = 0 := by
    rw [← hx] at hd
    linear_combination hd
  exact (IsLocalization.Away.algebraMap_isUnit h).pow n |>.mul_left_cancel
    (hz.trans (mul_zero _).symm)

/-- A genuine localized polynomial vector field. -/
def localizedVectorField (v : Fin N → CubicPolynomial N) : Derivation ℂ L L :=
  ∑ i, algebraMap (CubicPolynomial N) L (v i) • LocalizedPoisson.localizedPderiv S L i

@[simp] theorem localizedVectorField_apply (v : Fin N → CubicPolynomial N) (x : L) :
    localizedVectorField S L v x =
      ∑ i, algebraMap (CubicPolynomial N) L (v i) * LocalizedPoisson.localizedPderiv S L i x := by
  change (Derivation.coeFnAddMonoidHom (∑ i, algebraMap (CubicPolynomial N) L (v i) •
    LocalizedPoisson.localizedPderiv S L i)) x = _
  rw [map_sum]
  simp [Algebra.smul_def]

@[simp] theorem localizedEuler_apply (x : L) :
    localizedEuler S L x =
      ∑ i, algebraMap (CubicPolynomial N) L (X i) * LocalizedPoisson.localizedPderiv S L i x :=
  localizedVectorField_apply S L (fun i => X i) x

/-- Euler wedge representatives act by the determinant of the two genuine
localized vector-field actions. -/
theorem bracket_eulerWedge1 (v : Fin N → CubicPolynomial N) (x y : L) :
    LocalizedPoisson.bracket S L (eulerWedge1 v) x y =
      localizedEuler S L x * localizedVectorField S L v y -
        localizedVectorField S L v x * localizedEuler S L y := by
  simp only [LocalizedPoisson.bracket, eulerWedge1, map_sub, map_mul,
    localizedEuler_apply, localizedVectorField_apply, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/-- Euler-wedge ambiguity vanishes on every genuine projective degree-zero
function ring, for arbitrary polynomial vector coefficients. -/
theorem bracket_eulerWedge1_degreeZero {h : CubicPolynomial N} {d : ℕ}
    (hh : h.IsHomogeneous d) (v : Fin N → CubicPolynomial N)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h)
      (eulerWedge1 v) x.val y.val = 0 := by
  rw [bracket_eulerWedge1, localizedEuler_degreeZero hh x, localizedEuler_degreeZero hh y]
  simp

/-- Localized bracket evaluation is linear in its coefficient array. -/
theorem localizedBracket_add_coefficients
    (q r : Fin N → Fin N → CubicPolynomial N) (x y : L) :
    LocalizedPoisson.bracket S L (fun i j => q i j + r i j) x y =
      LocalizedPoisson.bracket S L q x y + LocalizedPoisson.bracket S L r x y := by
  simp [LocalizedPoisson.bracket, map_add, add_mul, Finset.sum_add_distrib]

/-- Euler-related polynomial representatives define exactly the same bracket
on every genuine degree-zero homogeneous localization. -/
theorem localizedBracket_eq_of_eulerWedge {h : CubicPolynomial N} {d : ℕ}
    (hh : h.IsHomogeneous d) (q r : Fin N → Fin N → CubicPolynomial N)
    (v : Fin N → CubicPolynomial N) (heq : ∀ i j, r i j = q i j + eulerWedge1 v i j)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) r x.val y.val =
      LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q x.val y.val := by
  have hr : r = fun i j => q i j + eulerWedge1 v i j := funext fun i => funext (heq i)
  rw [hr, localizedBracket_add_coefficients, bracket_eulerWedge1_degreeZero hh, add_zero]

/-- Actual projective basic-open brackets are independent of the Euler-wedge
choice of homogeneous quadratic representative. -/
theorem homogeneousBracket_eq_of_eulerWedge
    (q r : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, (q i j).IsHomogeneous 2) (hr : ∀ i j, (r i j).IsHomogeneous 2)
    (v : Fin N → CubicPolynomial N) (heq : ∀ i j, r i j = q i j + eulerWedge1 v i j)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    HomogeneousBasic.bracket r hr hd hh x y = HomogeneousBasic.bracket q hq hd hh x y := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousBasic.bracket_val, HomogeneousBasic.bracket_val]
  exact localizedBracket_eq_of_eulerWedge hh q r v heq x y
end NcCubic.Geometry
