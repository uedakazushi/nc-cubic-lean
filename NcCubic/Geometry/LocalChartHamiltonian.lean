module
public import NcCubic.Geometry.ConeBracket
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import StacksFrontier.RingTheory.Derivation.Localization
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- Cubic potentials give genuinely homogeneous quadratic contraction coefficients. -/
theorem contractionCoefficients_isHomogeneous
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3)
    (i j : Fin N) : (contractionCoefficients F P i j).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro a _
  exact (hF.pderiv (i := a)).C_mul _

/-- The polynomial Hamiltonian vector field as an actual derivation. -/
def polynomialHamiltonian (F : CubicPolynomial N) (P : Trivector N) (f : CubicPolynomial N) :
    Derivation ℂ (CubicPolynomial N) (CubicPolynomial N) :=
  ∑ i : Fin N, ∑ j : Fin N,
    (contractionCoefficients F P i j * pderiv i f) • pderiv j

@[simp] theorem polynomialHamiltonian_apply (F : CubicPolynomial N) (P : Trivector N)
    (f g : CubicPolynomial N) :
    polynomialHamiltonian F P f g = bracketFromCoefficients (contractionCoefficients F P) f g := by
  simp [polynomialHamiltonian, bracketFromCoefficients, Derivation.smul_apply]

@[simp] theorem polynomialHamiltonian_coordinates (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) : polynomialHamiltonian F P (X i) (X j) = contractionCoefficients F P i j := by
  simp [polynomialHamiltonian_apply, bracketFromCoefficients, pderiv_X, Pi.single_apply]

/-- The ambient affine ring before taking degree-zero functions on the projective chart. -/
abbrev ChartLocalization (i : Fin N) := Localization.Away (X i : CubicPolynomial N)

/-- The invertible chart denominator z_i, with its membership proof. -/
def chartDenominator (i : Fin N) : Submonoid.powers (X i : CubicPolynomial N) :=
  ⟨X i, Submonoid.mem_powers (X i)⟩

/-- The genuine ratio coordinate z_j/z_i in the localized ring. -/
def chartCoordinate (i j : Fin N) : ChartLocalization i :=
  IsLocalization.mk' (ChartLocalization i) (X j) (chartDenominator i)

/-- Extend a coordinate Hamiltonian to the actual localization at z_i. -/
def localizedCoordinateHamiltonian (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) : Derivation ℂ (ChartLocalization i) (ChartLocalization i) :=
  (polynomialHamiltonian F P (X j)).localization (Submonoid.powers (X i)) (ChartLocalization i)

/-- The ratio-coordinate Hamiltonian acts on the actual localization ring.
Preservation of its homogeneous degree-zero subring is a separate obligation. -/
def chartCoordinateHamiltonian (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) : Derivation ℂ (ChartLocalization i) (ChartLocalization i) :=
  (IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i)) •
      localizedCoordinateHamiltonian F P i j -
    (IsLocalization.mk' (ChartLocalization i) (X j)
      (chartDenominator i * chartDenominator i)) •
      localizedCoordinateHamiltonian F P i i

@[simp] theorem polynomialHamiltonian_potential (F : CubicPolynomial N) (P : Trivector N)
    (f : CubicPolynomial N) : polynomialHamiltonian F P f F = 0 := by
  rw [polynomialHamiltonian_apply, bracket_skew _ (contraction_skew F P),
    contraction_potential_casimir, neg_zero]

/-- Each localized coordinate Hamiltonian is genuinely tangent to the equation F. -/
@[simp] theorem localizedCoordinateHamiltonian_potential (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) : localizedCoordinateHamiltonian F P i j
      (algebraMap (CubicPolynomial N) (ChartLocalization i) F) = 0 := by
  change (polynomialHamiltonian F P (X j)).localization (Submonoid.powers (X i))
    (ChartLocalization i) (algebraMap (CubicPolynomial N) (ChartLocalization i) F) = 0
  rw [Derivation.localization_algebraMap, polynomialHamiltonian_potential, map_zero]

/-- Ratio-coordinate Hamiltonians still annihilate the localized defining equation. -/
@[simp] theorem chartCoordinateHamiltonian_potential (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) : chartCoordinateHamiltonian F P i j
      (algebraMap (CubicPolynomial N) (ChartLocalization i) F) = 0 := by
  simp [chartCoordinateHamiltonian]

/-- The quotient-rule formula on actual ratio coordinates. It records the
chart bivector coefficients before the degree-zero preservation/gluing step. -/
theorem chartCoordinateHamiltonian_coordinate (F : CubicPolynomial N) (P : Trivector N)
    (i j k : Fin N) :
    chartCoordinateHamiltonian F P i j (chartCoordinate i k) =
      IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) *
        IsLocalization.mk' (ChartLocalization i)
          (X i * contractionCoefficients F P j k - X k * contractionCoefficients F P j i)
          (chartDenominator i * chartDenominator i) -
      IsLocalization.mk' (ChartLocalization i) (X j) (chartDenominator i * chartDenominator i) *
        IsLocalization.mk' (ChartLocalization i)
          (X i * contractionCoefficients F P i k - X k * contractionCoefficients F P i i)
          (chartDenominator i * chartDenominator i) := by
  simp [chartCoordinateHamiltonian, chartCoordinate, localizedCoordinateHamiltonian,
    Derivation.localization_mk', chartDenominator, -polynomialHamiltonian_apply]

/-- Localized polynomial Hamiltonians commute with actual transition maps
between localizations. This is the ring-level overlap compatibility. -/
theorem localizedCoordinateHamiltonian_natural (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) {T : Submonoid (CubicPolynomial N)}
    {L : Type*} [CommRing L] [Algebra (CubicPolynomial N) L] [IsLocalization T L]
    [Algebra ℂ L] [IsScalarTower ℂ (CubicPolynomial N) L]
    (g : ChartLocalization i →ₐ[CubicPolynomial N] L) (x : ChartLocalization i) :
    g (localizedCoordinateHamiltonian F P i j x) =
      (polynomialHamiltonian F P (X j)).localization T L (g x) := by
  exact Stacks.DerivationExtension.algHom_locDeriv
    (S := Submonoid.powers (X i)) (T := T)
    ((polynomialHamiltonian F P (X j)).restrictScalars ℤ) (ChartLocalization i) L g x

/-- Ratio Hamiltonians commute with actual localization transition maps, with
both scalar fractions transported along the same map. -/
theorem chartCoordinateHamiltonian_natural (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) {T : Submonoid (CubicPolynomial N)}
    {L : Type*} [CommRing L] [Algebra (CubicPolynomial N) L] [IsLocalization T L]
    [Algebra ℂ L] [IsScalarTower ℂ (CubicPolynomial N) L]
    (g : ChartLocalization i →ₐ[CubicPolynomial N] L) (x : ChartLocalization i) :
    g (chartCoordinateHamiltonian F P i j x) =
      g (IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i)) *
        (polynomialHamiltonian F P (X j)).localization T L (g x) -
      g (IsLocalization.mk' (ChartLocalization i) (X j)
        (chartDenominator i * chartDenominator i)) *
        (polynomialHamiltonian F P (X i)).localization T L (g x) := by
  simp only [chartCoordinateHamiltonian, Derivation.sub_apply, Derivation.smul_apply,
    smul_eq_mul, map_sub, map_mul]
  rw [localizedCoordinateHamiltonian_natural F P i j (T := T) g x,
    localizedCoordinateHamiltonian_natural F P i i (T := T) g x]

/-- Tangency is ideal-theoretic: the whole principal ideal of the localized
hypersurface equation is stable under each ratio-coordinate Hamiltonian. -/
theorem chartCoordinateHamiltonian_preserves_equationIdeal
    (F : CubicPolynomial N) (P : Trivector N) (i j : Fin N)
    (x : ChartLocalization i)
    (hx : x ∈ Ideal.span ({algebraMap (CubicPolynomial N) (ChartLocalization i) F} :
      Set (ChartLocalization i))) :
    chartCoordinateHamiltonian F P i j x ∈
      Ideal.span ({algebraMap (CubicPolynomial N) (ChartLocalization i) F} :
        Set (ChartLocalization i)) := by
  rw [Ideal.mem_span_singleton] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  rw [Derivation.leibniz, chartCoordinateHamiltonian_potential]
  simp only [smul_eq_mul, mul_zero, add_zero]
  exact dvd_mul_right _ _

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine homogeneous degree-zero ring of a standard projective chart. -/
abbrev ProjectiveChartRing (i : Fin N) :=
  HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) (X i)
/-- The ratio-coordinate bracket numerator, homogeneous of degree three. -/
def ratioBracketNumerator (F : CubicPolynomial N) (P : Trivector N) (i j k : Fin N) :=
  X i * contractionCoefficients F P j k - X k * contractionCoefficients F P j i -
    X j * contractionCoefficients F P i k
theorem ratioBracketNumerator_homogeneous (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (i j k : Fin N) :
    (ratioBracketNumerator F P i j k).IsHomogeneous 3 := by
  exact (((isHomogeneous_X ℂ i).mul (contractionCoefficients_isHomogeneous F P hF j k)).sub
    ((isHomogeneous_X ℂ k).mul (contractionCoefficients_isHomogeneous F P hF j i))).sub
    ((isHomogeneous_X ℂ j).mul (contractionCoefficients_isHomogeneous F P hF i k))
/-- The ratio-coordinate coefficient as an actual degree-zero chart-ring element. -/
def projectiveBracketCoefficient (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (i j k : Fin N) : ProjectiveChartRing i :=
  HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin N) ℂ)
    (isHomogeneous_X ℂ i) 3 (ratioBracketNumerator F P i j k)
    (ratioBracketNumerator_homogeneous F P hF i j k)

/-- Its image in the ordinary localization is the expected cubic-over-cubic fraction. -/
theorem projectiveBracketCoefficient_val
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3)
    (i j k : Fin N) :
    (projectiveBracketCoefficient F P hF i j k).val =
      IsLocalization.mk' (ChartLocalization i) (ratioBracketNumerator F P i j k)
        (chartDenominator i ^ 3) := by
  change Localization.mk (ratioBracketNumerator F P i j k)
    ⟨X i ^ 3, by exact ⟨3, rfl⟩⟩ = _
  rw [Localization.mk_eq_mk']
  rfl

theorem projectiveBracketCoefficient_matches_hamiltonian
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3)
    (i j k : Fin N) :
    (projectiveBracketCoefficient F P hF i j k).val =
      chartCoordinateHamiltonian F P i j (chartCoordinate i k) := by
  have hdiag : contractionCoefficients F P i i = 0 :=
    CharZero.eq_neg_self_iff.mp (contraction_skew F P i i)
  have hp (n : ℕ) : IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i ^ n) =
      (IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i)) ^ n := by
    simpa using IsLocalization.mk'_pow (S := ChartLocalization i) 1 (chartDenominator i) n
  have hu : IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) *
      algebraMap (CubicPolynomial N) (ChartLocalization i) (X i) = 1 := by
    simp [chartDenominator]
  have hf (n : ℕ) (x : CubicPolynomial N) :
      IsLocalization.mk' (ChartLocalization i) x (chartDenominator i ^ n) =
      algebraMap (CubicPolynomial N) (ChartLocalization i) x *
        IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) ^ n := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hp]
  rw [projectiveBracketCoefficient_val, chartCoordinateHamiltonian_coordinate]
  simp only [hdiag, mul_zero, sub_zero, ← pow_two]
  rw [hf 3, hf 2, hf 2, hf 2]
  simp only [ratioBracketNumerator, map_sub, map_mul]
  linear_combination
    (algebraMap (CubicPolynomial N) (ChartLocalization i) (X j) *
      algebraMap (CubicPolynomial N) (ChartLocalization i) (contractionCoefficients F P i k) *
      IsLocalization.mk' (ChartLocalization i) 1 (chartDenominator i) ^ 3) * hu

end NcCubic.Geometry
