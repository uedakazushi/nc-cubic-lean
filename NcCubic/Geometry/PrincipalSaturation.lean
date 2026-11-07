/-
# Saturation of a principal polynomial ideal

Two distinct projective coordinates suffice: their powers have no common
nonunit divisor, so an entire homogeneous component multiplying `p` into `(F)`
forces `p ∈ (F)`. No smoothness or irreducibility of `F` is assumed.
-/
module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.PrincipalSaturation
open MvPolynomial
variable {K σ : Type*} [Field K]
lemma relprime_X (i j : σ) (hij : i ≠ j) : IsRelPrime (X i : MvPolynomial σ K) (X j) := by
  apply (X_prime (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
  simpa using hij

lemma relprime_powers {A : Type*} [CommMonoid A] [DecompositionMonoid A]
    {a b : A} (h : IsRelPrime a b) (m n : ℕ) : IsRelPrime (a^m) (b^n) := by
  have hright : IsRelPrime a (b^n) := by
    induction n with
    | zero => simpa using (isRelPrime_one_right : IsRelPrime a 1)
    | succ n hn => simpa only [pow_succ] using hn.mul_right h
  induction m with
  | zero => simpa using (isRelPrime_one_left : IsRelPrime 1 (b^n))
  | succ m hm => simpa only [pow_succ] using hm.mul_left hright

lemma dvd_of_two_mul {A : Type*} [CommMonoidWithZero A] [GCDMonoid A]
    {f a b x : A} (h : IsRelPrime a b) (ha : f ∣ a*x) (hb : f ∣ b*x) : f ∣ x := by
  have hu := gcd_isUnit_iff_isRelPrime.mpr h
  have hh := (dvd_gcd ha hb).trans (gcd_mul_right' x a b).dvd
  rwa [hu.dvd_mul_left] at hh

lemma principal_saturated_two_variables (i j : σ) (hij : i ≠ j)
    (F p : MvPolynomial σ K) (N : ℕ)
    (hi : F ∣ X i ^ N * p) (hj : F ∣ X j ^ N * p) : F ∣ p := by
  let := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial σ K)
  exact dvd_of_two_mul (relprime_powers (relprime_X i j hij) N N) hi hj

lemma principal_homogeneous_saturated (i j : σ) (hij : i ≠ j)
    (F p : MvPolynomial σ K)
    (h : ∃ N : ℕ, ∀ y : MvPolynomial σ K,
      y.IsHomogeneous N → y*p ∈ Ideal.span ({F} : Set _)) :
    p ∈ Ideal.span ({F} : Set _) := by
  obtain ⟨N,hN⟩ := h
  apply Ideal.mem_span_singleton.mpr
  apply principal_saturated_two_variables i j hij F p N
  · exact Ideal.mem_span_singleton.mp (hN _ (by simpa using (isHomogeneous_X K i).pow N))
  · exact Ideal.mem_span_singleton.mp (hN _ (by simpa using (isHomogeneous_X K j).pow N))

end NcCubic.Geometry.PrincipalSaturation
