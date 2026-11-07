/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.HomogeneousBasicBracket
public import NcCubic.Geometry.ProjectiveEquation
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.HomogeneousBasic
open MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {N : ℕ}

def rowNumerator (q : Fin N → Fin N → CubicPolynomial N)
    (h a : CubicPolynomial N) (n : ℕ) (i : Fin N) :=
  ∑ j, q i j * derivativeNumerator h a n j

theorem rowNumerator_homogeneous
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h a : CubicPolynomial N} {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (hh : h.IsHomogeneous d) (ha : a.IsHomogeneous (n*d)) (i : Fin N) :
    (rowNumerator q h a n i).IsHomogeneous ((n+1)*d+1) := by
  have hnD := Nat.mul_pos (by omega : 0 < n+1) hd
  unfold rowNumerator
  apply IsHomogeneous.sum
  intro j _
  convert (hq i j).mul (derivativeNumerator_homogeneous hd hn hh ha j) using 1
  omega

theorem bracket_X (q : Fin N → Fin N → CubicPolynomial N)
    (h : CubicPolynomial N) (i : Fin N) (x : Localization.Away h) :
    LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q
      (algebraMap (CubicPolynomial N) (Localization.Away h) (X i)) x =
    ∑ j, algebraMap (CubicPolynomial N) (Localization.Away h) (q i j) *
      LocalizedPoisson.localizedPderiv (Submonoid.powers h) (Localization.Away h) j x := by
  simp [LocalizedPoisson.bracket,LocalizedPoisson.localizedPderiv,pderiv_X,Pi.single_apply]

theorem row_cleared (q : Fin N → Fin N → CubicPolynomial N)
    {h a : CubicPolynomial N} {n : ℕ} (hn : 0 < n) (i : Fin N)
    (x : Localization.Away h)
    (hx : (algebraMap (CubicPolynomial N) (Localization.Away h) h)^n*x = algebraMap (CubicPolynomial N) (Localization.Away h) a) :
    (algebraMap (CubicPolynomial N) (Localization.Away h) h)^(n+1) *
      LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q
        (algebraMap (CubicPolynomial N) (Localization.Away h) (X i)) x = algebraMap (CubicPolynomial N) (Localization.Away h) (rowNumerator q h a n i) := by
  rw [bracket_X]
  simp only [rowNumerator,map_sum,Finset.mul_sum,map_mul]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = algebraMap (CubicPolynomial N) (Localization.Away h) (q i j) *
      ((algebraMap (CubicPolynomial N) (Localization.Away h) h)^(n+1) *
        LocalizedPoisson.localizedPderiv (Submonoid.powers h) (Localization.Away h) j x) := by ring
    _ = _ := by rw [derivative_cleared hn x hx j]

/-- Logarithmic coordinate Hamiltonians preserve every positive homogeneous
basic refinement inside the coordinate chart: [z_i,a]/z_i is degree zero. -/
theorem exists_logHamiltonian
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    (i : Fin N) {g h : CubicPolynomial N} {e : ℕ}
    (hg : g.IsHomogeneous e) (hx : h = X i*g)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    ∃ z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h,
      algebraMap (CubicPolynomial N) (Localization.Away h) (X i) * z.val =
        LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q
          (algebraMap (CubicPolynomial N) (Localization.Away h) (X i)) x.val := by
  classical
  have hh : h.IsHomogeneous (1+e) := hx ▸ (isHomogeneous_X ℂ i).mul hg
  obtain ⟨n,a,hn,ha,hxa⟩ := exists_positive_rep hh x
  let A := g * rowNumerator q h a n i
  have hA : A ∈ homogeneousSubmodule (Fin N) ℂ ((n+2) • (1+e)) := by
    change A.IsHomogeneous ((n+2) • (1+e))
    simp only [nsmul_eq_mul,Nat.cast_id]
    convert hg.mul (rowNumerator_homogeneous q hq (by omega) hn hh ha i) using 1
    ring
  let z := HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin N) ℂ) hh (n+2) A hA
  refine ⟨z,?_⟩
  let t := algebraMap (CubicPolynomial N) (Localization.Away h) h
  have hz : t^(n+2)*z.val = algebraMap (CubicPolynomial N) (Localization.Away h) A := by
    change _ * Localization.mk A (⟨h^(n+2),by exact ⟨n+2,rfl⟩⟩ : Submonoid.powers h) = _
    rw [Localization.mk_eq_mk']
    simpa only [t,map_pow,mul_comm] using
      (IsLocalization.mk'_spec (Localization.Away h) A
        (⟨h^(n+2),by exact ⟨n+2,rfl⟩⟩ : Submonoid.powers h))
  have hrow := row_cleared q hn i x.val hxa
  have hu : IsUnit (t^(n+2)) := (IsLocalization.Away.algebraMap_isUnit h).pow (n+2)
  apply hu.mul_left_cancel
  calc
    _ = algebraMap (CubicPolynomial N) (Localization.Away h) (X i) * (t^(n+2)*z.val) := by ring
    _ = algebraMap (CubicPolynomial N) (Localization.Away h) (X i) * algebraMap (CubicPolynomial N) (Localization.Away h) g * algebraMap (CubicPolynomial N) (Localization.Away h) (rowNumerator q h a n i) := by
      rw [hz]
      simp only [A,map_mul,mul_assoc]
    _ = t * algebraMap (CubicPolynomial N) (Localization.Away h) (rowNumerator q h a n i) := by rw [← map_mul,← hx]
    _ = t * (t^(n+1) * LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q
      (algebraMap (CubicPolynomial N) (Localization.Away h) (X i)) x.val) := by rw [hrow]
    _ = _ := by rw [show n+2=(n+1)+1 by omega,pow_succ']; ring
/-- The actual normalized cubic equation on a homogeneous basic refinement
inside the coordinate chart. -/
def normalizedEquation (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (i : Fin N)
    {g h : CubicPolynomial N} {e : ℕ} (hg : g.IsHomogeneous e) (hx : h = X i*g) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h :=
  restriction hg hx (projectiveEquation F hF i)

theorem normalizedEquation_relation (F : CubicPolynomial N) (hF : F.IsHomogeneous 3) (i : Fin N)
    {g h : CubicPolynomial N} {e : ℕ} (hg : g.IsHomogeneous e) (hx : h = X i*g) :
    (algebraMap (CubicPolynomial N) (Localization.Away h) (X i))^3 *
      (normalizedEquation F hF i hg hx).val = algebraMap (CubicPolynomial N) (Localization.Away h) F := by
  have hs : (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i))^3 *
      (projectiveEquation F hF i).val = algebraMap (CubicPolynomial N) (ChartLocalization i) F := by
    change _ * Localization.mk F (⟨(X i)^3,by exact ⟨3,rfl⟩⟩ : Submonoid.powers (X i)) = _
    rw [Localization.mk_eq_mk']
    have hs0 := IsLocalization.mk'_spec (ChartLocalization i) F
      (⟨(X i)^3,by exact ⟨3,rfl⟩⟩ : Submonoid.powers (X i))
    rw [map_pow] at hs0
    exact (mul_comm _ _).trans hs0
  have ht := congrArg (ambientRestriction hx) hs
  simpa only [normalizedEquation,restriction_val,map_mul,map_pow,AlgHom.commutes] using ht

/-- The normalized equation is preserved with a genuine degree-zero
multiplier on every homogeneous refinement, not merely at ratio generators. -/
theorem normalizedEquation_bracket
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3) (i : Fin N)
    {g h : CubicPolynomial N} {e : ℕ} (hg : g.IsHomogeneous e) (hx : h = X i*g)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    ∃ z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h,
      bracket (contractionCoefficients F P) (contractionCoefficients_isHomogeneous F P hF)
        (by omega : 0 < 1+e) (hx ▸ (isHomogeneous_X ℂ i).mul hg)
        (normalizedEquation F hF i hg hx) x = -3*z*normalizedEquation F hF i hg hx := by
  let q := contractionCoefficients F P
  let L := Localization.Away h
  let t : L := algebraMap (CubicPolynomial N) L (X i)
  let E := normalizedEquation F hF i hg hx
  obtain ⟨z,hz⟩ := exists_logHamiltonian q (contractionCoefficients_isHomogeneous F P hF) i hg hx x
  refine ⟨z,?_⟩
  have hE : t^3*E.val = algebraMap (CubicPolynomial N) L F := normalizedEquation_relation F hF i hg hx
  have ht : LocalizedPoisson.bracket (Submonoid.powers h) L q (t^3) x.val =
      3*t^2*LocalizedPoisson.bracket (Submonoid.powers h) L q t x.val := by
    simp only [pow_succ,pow_zero,one_mul,
      LocalizedPoisson.bracket_mul_left q (contraction_skew F P)]
    ring
  have hB := congrArg (fun a : L => LocalizedPoisson.bracket (Submonoid.powers h) L q a x.val) hE
  rw [LocalizedPoisson.bracket_mul_left q (contraction_skew F P),ht,
    LocalizedPoisson.bracket_potential F P] at hB
  change t*z.val = LocalizedPoisson.bracket (Submonoid.powers h) L q t x.val at hz
  rw [← hz] at hB
  have hu : IsUnit (t^3) := (isUnit_of_dvd_unit
    (map_dvd (algebraMap (CubicPolynomial N) L) (show (X i : CubicPolynomial N) ∣ h from ⟨g,hx⟩))
    (IsLocalization.Away.algebraMap_isUnit h)).pow 3
  apply HomogeneousLocalization.val_injective
  have hv3 : (3 : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h).val = 3 :=
    HomogeneousLocalization.val_natCast 3
  simp only [bracket_val,HomogeneousLocalization.val_mul,HomogeneousLocalization.val_neg,hv3]
  apply hu.mul_left_cancel
  change t^3*LocalizedPoisson.bracket (Submonoid.powers h) L q E.val x.val = t^3*(-3*z.val*E.val)
  linear_combination hB

/-- The actual equation ideal on every positive homogeneous basic refinement
is stable under the full bracket in arbitrary arguments. -/
theorem bracket_preserves_normalizedEquationIdeal
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3) (i : Fin N)
    {g h : CubicPolynomial N} {e : ℕ} (hg : g.IsHomogeneous e) (hx : h = X i*g)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h)
    (hy : y ∈ Ideal.span ({normalizedEquation F hF i hg hx} : Set _)) :
    bracket (contractionCoefficients F P) (contractionCoefficients_isHomogeneous F P hF)
        (by omega : 0 < 1+e) (hx ▸ (isHomogeneous_X ℂ i).mul hg) x y ∈
      Ideal.span ({normalizedEquation F hF i hg hx} : Set _) := by
  let q := contractionCoefficients F P
  let hq := contractionCoefficients_isHomogeneous F P hF
  let hh := hx ▸ (isHomogeneous_X ℂ i).mul hg
  let E := normalizedEquation F hF i hg hx
  let I := Ideal.span ({E} : Set (HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h))
  have hE : bracket q hq (by omega : 0 < 1+e) hh x E ∈ I := by
    obtain ⟨z,hz⟩ := normalizedEquation_bracket F P hF i hg hx x
    rw [bracket_skew q hq (contraction_skew F P),hz]
    apply I.neg_mem
    exact Ideal.mem_span_singleton.mpr (dvd_mul_left E (-3*z))
  rw [Ideal.mem_span_singleton] at hy
  obtain ⟨a,rfl⟩ := hy
  rw [bracket_leibniz]
  exact I.add_mem (Ideal.mem_span_singleton.mpr (dvd_mul_right E _)) (I.mul_mem_left a hE)
end NcCubic.Geometry.HomogeneousBasic
