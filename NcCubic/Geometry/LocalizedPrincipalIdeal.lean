/- Clearing projective chart denominators in a principal ideal.
Two distinct coordinate localizations detect global divisibility. -/
module
public import NcCubic.Geometry.PrincipalSaturation
public import Mathlib.RingTheory.Localization.Ideal
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.LocalizedPrincipalIdeal
open MvPolynomial
/-- Membership in a localized principal ideal clears a power of the denominator. -/
lemma exists_pow_mul_dvd_of_localized_mem {R : Type*} [CommRing R]
    (f F W : R)
    (h : algebraMap R (Localization.Away f) W ∈ Ideal.span
      ({algebraMap R (Localization.Away f) F} : Set (Localization.Away f))) :
    ∃ m : ℕ, F ∣ f^m * W := by
  have hm : algebraMap R (Localization.Away f) W ∈
      (Ideal.span ({F} : Set R)).map (algebraMap R (Localization.Away f)) := by
    simpa only [Ideal.map_span, Set.image_singleton] using h
  obtain ⟨s, hs, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) (Localization.Away f)
      (Ideal.span ({F} : Set R)) W).mp hm
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff s f).mp hs
  exact ⟨m, Ideal.mem_span_singleton.mp hmem⟩

/-- Two distinct coordinate charts suffice to detect global principal-ideal membership. -/
lemma dvd_of_two_localizations {K σ : Type*} [Field K]
    (i j : σ) (hij : i ≠ j) (F W : MvPolynomial σ K)
    (hi : algebraMap (MvPolynomial σ K) (Localization.Away (X i : MvPolynomial σ K)) W ∈ Ideal.span
      ({algebraMap (MvPolynomial σ K) (Localization.Away (X i : MvPolynomial σ K)) F} : Set (Localization.Away (X i : MvPolynomial σ K))))
    (hj : algebraMap (MvPolynomial σ K) (Localization.Away (X j : MvPolynomial σ K)) W ∈ Ideal.span
      ({algebraMap (MvPolynomial σ K) (Localization.Away (X j : MvPolynomial σ K)) F} : Set (Localization.Away (X j : MvPolynomial σ K)))) :
    F ∣ W := by
  obtain ⟨m, hm⟩ := exists_pow_mul_dvd_of_localized_mem (X i) F W hi
  obtain ⟨n, hn⟩ := exists_pow_mul_dvd_of_localized_mem (X j) F W hj
  let := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial σ K)
  exact PrincipalSaturation.dvd_of_two_mul
    (PrincipalSaturation.relprime_powers (PrincipalSaturation.relprime_X i j hij) m n) hm hn
end NcCubic.Geometry.LocalizedPrincipalIdeal
