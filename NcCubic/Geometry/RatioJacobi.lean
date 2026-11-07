module
public import NcCubic.Geometry.LocalizedBracket
public import NcCubic.Geometry.LocalChartHamiltonian
public import NcCubic.Geometry.EulerJacobiLift
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}
namespace LocalizedPoisson
variable {S : Submonoid (CubicPolynomial N)} {L : Type*} [CommRing L]
  [Algebra (CubicPolynomial N) L] [IsLocalization S L] [Algebra ℂ L]
  [IsScalarTower ℂ (CubicPolynomial N) L]

theorem jacobiator_swap_first (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (a b c : L) :
    jacobiator (S:=S) q a b c = -jacobiator (S:=S) q b a c := by
  unfold jacobiator
  rw [bracket_skew q hq b a,bracket_skew q hq c b,bracket_skew q hq a c]
  simp only [bracket_neg_right]
  ring

theorem jacobiator_self (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (a b : L) : jacobiator (S:=S) q a a b = 0 := by
  unfold jacobiator
  rw [bracket_skew q hq b a,bracket_neg_right,bracket_self q hq a,bracket_zero_right]
  ring

theorem jacobiator_self_last (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (a b : L) : jacobiator (S:=S) q a b b = 0 := by
  rw [jacobiator_cyclic]
  exact jacobiator_self q hq b a

theorem jacobiator_self_outer (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (a b : L) : jacobiator (S:=S) q a b a = 0 := by
  rw [← jacobiator_cyclic q a a b]
  exact jacobiator_self q hq a b

theorem jacobiator_coordinates (q : Fin N → Fin N → CubicPolynomial N) (i j k : Fin N) :
    jacobiator (S:=S) q (algebraMap (CubicPolynomial N) L (X i)) (algebraMap (CubicPolynomial N) L (X j)) (algebraMap (CubicPolynomial N) L (X k)) =
      algebraMap (CubicPolynomial N) L (jacobiArray q i j k) := by
  simp only [jacobiator,bracket_algebraMap]
  simp only [JacobiCriterion.bracket_coordinates]
  simp only [JacobiCriterion.bracket_coordinate_left,jacobiArray,Finset.sum_add_distrib,map_add]
end LocalizedPoisson

/-- The localized Jacobiator obeys a quotient rule in every variable. -/
theorem ratioJacobi_clear_first (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (i j : Fin N) (a b : ChartLocalization i) :
    algebraMap (CubicPolynomial N) (ChartLocalization i) (X i) *
      LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q (chartCoordinate i j) a b =
    LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q
      (algebraMap (CubicPolynomial N) (ChartLocalization i) (X j)) a b - chartCoordinate i j *
      LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q
        (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)) a b := by
  have hr : algebraMap (CubicPolynomial N) (ChartLocalization i) (X i) * chartCoordinate i j =
      algebraMap (CubicPolynomial N) (ChartLocalization i) (X j) := by
    simpa only [chartCoordinate,chartDenominator,mul_comm] using
      (IsLocalization.mk'_spec (ChartLocalization i) (X j) (chartDenominator i))
  have h := LocalizedPoisson.jacobiator_mul (S:=Submonoid.powers (X i)) q hq
    (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)) (chartCoordinate i j) a b
  rw [hr] at h
  linear_combination -h

theorem ratioJacobi_clear_second (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (i j : Fin N) (a b : ChartLocalization i) :
    algebraMap (CubicPolynomial N) (ChartLocalization i) (X i) *
      LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q a (chartCoordinate i j) b =
    LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q a
      (algebraMap (CubicPolynomial N) (ChartLocalization i) (X j)) b - chartCoordinate i j *
      LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q a
        (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)) b := by
  rw [LocalizedPoisson.jacobiator_cyclic q a (chartCoordinate i j) b]
  rw [ratioJacobi_clear_first q hq]
  rw [← LocalizedPoisson.jacobiator_cyclic q a (algebraMap (CubicPolynomial N) (ChartLocalization i) (X j)) b,
    ← LocalizedPoisson.jacobiator_cyclic q a (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)) b]

theorem ratioJacobi_clear_third (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (i j : Fin N) (a b : ChartLocalization i) :
    algebraMap (CubicPolynomial N) (ChartLocalization i) (X i) *
      LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q a b (chartCoordinate i j) =
    LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q a b
      (algebraMap (CubicPolynomial N) (ChartLocalization i) (X j)) - chartCoordinate i j *
      LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q a b
        (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)) := by
  rw [← LocalizedPoisson.jacobiator_cyclic q (chartCoordinate i j) a b]
  rw [ratioJacobi_clear_first q hq]
  rw [LocalizedPoisson.jacobiator_cyclic q (algebraMap (CubicPolynomial N) (ChartLocalization i) (X j)) a b,
    LocalizedPoisson.jacobiator_cyclic q (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)) a b]

/-- The actual ratio-coordinate Jacobiator is the Euler-wedge Jacobi tensor
divided by the fourth power of the chart coordinate. -/
theorem ratioJacobi_eulerWedge
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,q j i = -q i j)
    (i j k l : Fin N) :
    (algebraMap (CubicPolynomial N) (ChartLocalization i) (X i))^4 *
      LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) q
        (chartCoordinate i j) (chartCoordinate i k) (chartCoordinate i l) =
    algebraMap (CubicPolynomial N) (ChartLocalization i) (eulerWedge3 (jacobiArray q) i j k l) := by
  let t := algebraMap (CubicPolynomial N) (ChartLocalization i) (X i)
  let A := algebraMap (CubicPolynomial N) (ChartLocalization i) (X j)
  let B := algebraMap (CubicPolynomial N) (ChartLocalization i) (X k)
  let C := algebraMap (CubicPolynomial N) (ChartLocalization i) (X l)
  let r := chartCoordinate i j
  let s := chartCoordinate i k
  let u := chartCoordinate i l
  let J := LocalizedPoisson.jacobiator (S:=Submonoid.powers (X i)) (L:=ChartLocalization i) q
  have h1 := ratioJacobi_clear_first q hq i j s u
  have h2 := ratioJacobi_clear_second q hq i k A u
  have h3 := ratioJacobi_clear_third q hq i l A B
  have h4 := ratioJacobi_clear_third q hq i l A t
  have h5 := ratioJacobi_clear_second q hq i k t u
  have h6 := ratioJacobi_clear_third q hq i l t B
  rw [LocalizedPoisson.jacobiator_self_last q hq] at h4
  rw [LocalizedPoisson.jacobiator_self q hq] at h5
  rw [LocalizedPoisson.jacobiator_self_outer q hq] at h6
  simp only [mul_zero,sub_zero] at h4 h5 h6
  have hc : t^3*J r s u = J A B C-u*J A B t-s*J A t C-r*J t B C := by
    linear_combination t^2*h1+t*h2+h3-s*h4-t*r*h5-r*h6
  have hcyc : J A B t = J t A B := (LocalizedPoisson.jacobiator_cyclic q t A B).symm
  have hswap : J A t C = -J t A C := LocalizedPoisson.jacobiator_swap_first q hq A t C
  rw [hcyc,hswap] at hc
  have hr (j : Fin N) : t*chartCoordinate i j =
      algebraMap (CubicPolynomial N) (ChartLocalization i) (X j) := by
    simpa only [t,chartCoordinate,chartDenominator,mul_comm] using
      (IsLocalization.mk'_spec (ChartLocalization i) (X j) (chartDenominator i))
  have hfinal : t^4*J r s u = t*J A B C-A*J t B C+B*J t A C-C*J t A B := by
    linear_combination t*hc-J t B C*hr j+J t A C*hr k-J t A B*hr l
  change t^4*J r s u = _
  rw [hfinal]
  simp only [t,A,B,C,J,LocalizedPoisson.jacobiator_coordinates,eulerWedge3,map_sub,map_add,map_mul]
end NcCubic.Geometry
