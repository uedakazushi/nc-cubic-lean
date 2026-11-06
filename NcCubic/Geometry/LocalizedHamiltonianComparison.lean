/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.LocalizedBracket
public import NcCubic.Geometry.LocalChartHamiltonian
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- On polynomial inputs, the full localized Hamiltonian is precisely the
unique localization of the ambient polynomial Hamiltonian. -/
theorem localizedHamiltonian_algebraMap
    (F : CubicPolynomial N) (P : Trivector N) (f : CubicPolynomial N)
    (S : Submonoid (CubicPolynomial N)) (L : Type*) [CommRing L]
    [Algebra (CubicPolynomial N) L] [IsLocalization S L] [Algebra ℂ L]
    [IsScalarTower ℂ (CubicPolynomial N) L] :
    LocalizedPoisson.hamiltonian (S:=S) (contractionCoefficients F P)
      (algebraMap (CubicPolynomial N) L f) = (polynomialHamiltonian F P f).localization S L := by
  apply Derivation.ext_of_isLocalization S L
  intro g
  simp only [LocalizedPoisson.hamiltonian_apply,LocalizedPoisson.bracket_algebraMap,
    Derivation.localization_algebraMap,polynomialHamiltonian_apply]

/-- The full bracket on a ratio agrees with the previously constructed
ratio-coordinate Hamiltonian on every localized function. -/
theorem localizedBracket_chartCoordinate
    (F : CubicPolynomial N) (P : Trivector N) (i j : Fin N) (x : ChartLocalization i) :
    LocalizedPoisson.bracket (Submonoid.powers (X i : CubicPolynomial N)) (ChartLocalization i)
      (contractionCoefficients F P) (chartCoordinate i j) x =
    chartCoordinateHamiltonian F P i j x := by
  let S := Submonoid.powers (X i : CubicPolynomial N)
  let L := ChartLocalization i
  let t : L := algebraMap (CubicPolynomial N) L (X i)
  let r : L := chartCoordinate i j
  let u : L := IsLocalization.mk' L 1 (chartDenominator i)
  have hu : u * t = 1 := by
    simpa only [u,t,chartDenominator,map_one] using
      (IsLocalization.mk'_spec L 1 (chartDenominator i))
  have hr : t * r = algebraMap (CubicPolynomial N) L (X j) := by
    simpa only [t,r,chartCoordinate,chartDenominator,mul_comm] using
      (IsLocalization.mk'_spec L (X j) (chartDenominator i))
  have hfrac : IsLocalization.mk' L (X j) (chartDenominator i * chartDenominator i) = r*u := by
    simpa only [mul_one,r,u,chartCoordinate] using
      (IsLocalization.mk'_mul L (X j) 1 (chartDenominator i) (chartDenominator i))
  have hb (a : Fin N) : LocalizedPoisson.bracket S L (contractionCoefficients F P)
      (algebraMap (CubicPolynomial N) L (X a)) x = localizedCoordinateHamiltonian F P i a x := by
    rw [← LocalizedPoisson.hamiltonian_apply]
    rw [localizedHamiltonian_algebraMap]
    rfl
  have hmul := LocalizedPoisson.bracket_mul_left (S:=S) (contractionCoefficients F P)
    (contraction_skew F P) t r x
  rw [hr,hb,hb] at hmul
  change LocalizedPoisson.bracket S L (contractionCoefficients F P) r x = _
  simp only [chartCoordinateHamiltonian,Derivation.sub_apply,Derivation.smul_apply,
    smul_eq_mul]
  rw [hfrac]
  change LocalizedPoisson.bracket S L (contractionCoefficients F P) r x =
    u * localizedCoordinateHamiltonian F P i j x -
      (r*u) * localizedCoordinateHamiltonian F P i i x
  calc
    _ = (u*t) * LocalizedPoisson.bracket S L (contractionCoefficients F P) r x := by rw [hu,one_mul]
    _ = u * (localizedCoordinateHamiltonian F P i j x -
      r * localizedCoordinateHamiltonian F P i i x) := by linear_combination -u * hmul
    _ = _ := by ring
end NcCubic.Geometry
