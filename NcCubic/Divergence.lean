/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Coordinates
public import NcCubic.GradientContraction
public import NcCubic.JacobiCriterion
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic
open MvPolynomial
open scoped BigOperators

/-- Coordinate divergence of a polynomial bivector, with the contracted index first. -/
def divergence2 {N : ℕ} (q : Fin N → Fin N → CubicPolynomial N) (j : Fin N) :=
  ∑ a, pderiv a (q a j)

/-- Coordinate divergence of a polynomial trivector. -/
def divergence3 {N : ℕ} (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (i j : Fin N) := ∑ a, pderiv a (J a i j)

/-- Exterior product with the Euler vector field in degree one. -/
def eulerWedge1 {N : ℕ} (v : Fin N → CubicPolynomial N) (i j : Fin N) :=
  X i * v j - X j * v i

/-- Exterior product with the Euler vector field in degree two. -/
def eulerWedge2 {N : ℕ} (B : Fin N → Fin N → CubicPolynomial N) (i j k : Fin N) :=
  X i * B j k - X j * B i k + X k * B i j

/-- Constant alternating trivectors contracted with a gradient are divergence-free. -/
theorem divergence2_contraction {N : ℕ} (F : CubicPolynomial N) (P : Trivector N)
    (j : Fin N) : divergence2 (contractionCoefficients F P) j = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  simp only [divergence2, contractionCoefficients, map_sum, pderiv_mul,
    pderiv_C, zero_mul, zero_add]
  conv_lhs => rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [trivectorCoefficient_swap_last, map_neg, pderiv_comm]
  ring

/-- Euler's divergence identity for a homogeneous quadratic bivector.
All coefficients are explicit; no geometric lift is assumed. -/
theorem divergence3_eulerWedge2 {N : ℕ}
    (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j)
    (hdegree : ∀ i j, (B i j).IsHomogeneous 2) (i j : Fin N) :
    divergence3 (eulerWedge2 B) i j =
      N • B i j - eulerWedge1 (divergence2 B) i j := by
  classical
  simp only [divergence3, eulerWedge2, map_add, map_sub, pderiv_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [pderiv_X_self, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hfirst : ∑ a : Fin N, X a * pderiv a (B i j) = 2 • B i j :=
    (hdegree i j).sum_X_mul_pderiv
  have hi : ∑ a : Fin N, pderiv a (X i) * B a j = B i j := by
    simp [pderiv_X, Pi.single_apply]
  have hj : ∑ a : Fin N, pderiv a (X j) * B a i = B j i := by
    simp [pderiv_X, Pi.single_apply]
  rw [hfirst, hi, hj, hskew]
  simp only [divergence2, eulerWedge1, Finset.mul_sum, nsmul_eq_mul]
  ring

/-- Multiplying a constant trivector by the defining polynomial and taking
its divergence gives its contraction with the gradient. -/
theorem divergence3_polynomial_trivector {N : ℕ} (F : CubicPolynomial N)
    (P : Trivector N) (i j : Fin N) :
    divergence3 (fun a b c => F * C (trivectorCoefficient P a b c)) i j =
      contractionCoefficients F P i j := by
  simp only [divergence3, contractionCoefficients, pderiv_mul, pderiv_C,
    mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro a _
  rw [trivectorCoefficient_swap_last P j i a,
    trivectorCoefficient_swap_first P i j a, neg_neg]
  ring

/-- Divergence squares to zero, expressed entirely in alternating coefficients. -/
theorem divergence2_divergence3 {N : ℕ}
    (J : Fin N → Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ a b c, J b a c = -J a b c) (j : Fin N) :
    divergence2 (divergence3 J) j = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  simp only [divergence2, divergence3, map_sum]
  conv_lhs => rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hskew, map_neg, map_neg, pderiv_comm]

end NcCubic

namespace NcCubic
open MvPolynomial
open scoped BigOperators

def gradientContract3 {N : ℕ} (F : CubicPolynomial N)
    (J : Fin N → Fin N → Fin N → CubicPolynomial N) (i j : Fin N) :=
  ∑ a, pderiv a F * J a i j

/-- Euler wedge contraction on a bivector annihilating the gradient. -/
theorem gradientContract3_eulerWedge2 {N : ℕ} (F : CubicPolynomial N)
    (hF : F.IsHomogeneous 3) (B : Fin N → Fin N → CubicPolynomial N)
    (hcasimir : ∀ j, ∑ a, B a j * pderiv a F = 0) (i j : Fin N) :
    gradientContract3 F (eulerWedge2 B) i j = 3 * F * B i j := by
  classical
  have hc (j) : ∑ a, pderiv a F * B a j = 0 := by
    simpa only [mul_comm] using hcasimir j
  simp only [gradientContract3, eulerWedge2, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hterm : (∑ a, pderiv a F * (X a * B i j)) = 3 * F * B i j := by
    calc
      _ = (∑ a, X a * pderiv a F) * B i j := by
        simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; ring
      _ = _ := by rw [hF.sum_X_mul_pderiv]; simp [nsmul_eq_mul]
  have ht (u v) : (∑ a, pderiv a F * (X u * B a v)) = 0 := by
    calc
      _ = X u * ∑ a, pderiv a F * B a v := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      _ = 0 := by rw [hc, mul_zero]
  rw [hterm, ht, ht, sub_zero, add_zero]

/-- Taking Euler wedge removes the divergence-of-bivector term. -/
theorem euler_relation_of_divergence_lift {N : ℕ} (F : CubicPolynomial N)
    (T : Trivector N) (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j)
    (hdegree : ∀ i j, (B i j).IsHomogeneous 2)
    (hclosed : ∀ i j, divergence3 (fun a b c =>
      F * C (trivectorCoefficient T a b c) + eulerWedge2 B a b c) i j = 0)
    (i j k : Fin N) :
    eulerWedge2 (contractionCoefficients F T) i j k +
      N • eulerWedge2 B i j k = 0 := by
  have hh (u v) : contractionCoefficients F T u v +
      (N • B u v - eulerWedge1 (divergence2 B) u v) = 0 := by
    have hz := hclosed u v
    simp only [divergence3, map_add, Finset.sum_add_distrib] at hz
    change divergence3 (fun a b c => F * C (trivectorCoefficient T a b c)) u v +
      divergence3 (eulerWedge2 B) u v = 0 at hz
    rw [divergence3_polynomial_trivector, divergence3_eulerWedge2 B hskew hdegree] at hz
    exact hz
  simp only [eulerWedge2, eulerWedge1, nsmul_eq_mul] at *
  linear_combination X i * hh j k - X j * hh i k + X k * hh i j

end NcCubic

namespace NcCubic
open MvPolynomial
open scoped BigOperators

theorem gradientContract3_add {N : ℕ} (F : CubicPolynomial N)
    (A B : Fin N → Fin N → Fin N → CubicPolynomial N) (i j : Fin N) :
    gradientContract3 F (fun a b c => A a b c + B a b c) i j =
      gradientContract3 F A i j + gradientContract3 F B i j := by
  simp [gradientContract3, mul_add, Finset.sum_add_distrib]

theorem gradientContract3_mul {N : ℕ} (F c : CubicPolynomial N)
    (A : Fin N → Fin N → Fin N → CubicPolynomial N) (i j : Fin N) :
    gradientContract3 F (fun a b d => c * A a b d) i j =
      c * gradientContract3 F A i j := by
  simp [gradientContract3, Finset.mul_sum, mul_left_comm]

theorem gradientContract3_constant_trivector {N : ℕ} (F : CubicPolynomial N)
    (T : Trivector N) (i j : Fin N) :
    gradientContract3 F (fun a b c => C (trivectorCoefficient T a b c)) i j =
      contractionCoefficients F T i j := by
  unfold gradientContract3 contractionCoefficients
  dsimp only
  apply Finset.sum_congr rfl
  intro a _
  rw [trivectorCoefficient_swap_last T j i a,
    trivectorCoefficient_swap_first T i j a, neg_neg]
  ring

end NcCubic

namespace NcCubic
open MvPolynomial
open scoped BigOperators

/-- Algebraic core of Proposition 2.4. The geometric lift decomposition is
an explicit hypothesis; once supplied, its closed horizontal lift vanishes. -/
theorem divergence_lift_vanishes {N : ℕ} (hN : 5 ≤ N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (T : Trivector N)
    (B : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, B j i = -B i j)
    (hdegree : ∀ i j, (B i j).IsHomogeneous 2)
    (hclosed : ∀ i j, divergence3 (fun a b c =>
      F * C (trivectorCoefficient T a b c) + eulerWedge2 B a b c) i j = 0)
    (hhorizontal : ∀ i j, gradientContract3 F (fun a b c =>
      F * C (trivectorCoefficient T a b c) + eulerWedge2 B a b c) i j = 0) :
    ∀ i j k, F * C (trivectorCoefficient T i j k) + eulerWedge2 B i j k = 0 := by
  classical
  have hQ (i j) : contractionCoefficients F T i j = 0 := by
    have hr := euler_relation_of_divergence_lift F T B hskew hdegree hclosed
    have hsum := congrArg (fun v : Fin N → CubicPolynomial N =>
      ∑ a, pderiv a F * v a) (funext (fun a => hr a i j))
    simp only [mul_zero, Finset.sum_const_zero, nsmul_eq_mul] at hsum
    change gradientContract3 F (fun a b c =>
      eulerWedge2 (contractionCoefficients F T) a b c +
        (N : CubicPolynomial N) * eulerWedge2 B a b c) i j = 0 at hsum
    rw [gradientContract3_add, gradientContract3_mul,
      gradientContract3_eulerWedge2 F hF _ (contraction_gradient_zero F T)] at hsum
    have hz := hhorizontal i j
    rw [gradientContract3_add, gradientContract3_mul,
      gradientContract3_constant_trivector] at hz
    have hp : (3 - (N : CubicPolynomial N)) * F * contractionCoefficients F T i j = 0 := by
      linear_combination hsum - (N : CubicPolynomial N) * hz
    have hn3 : (N : CubicPolynomial N) ≠ 3 := by
      exact_mod_cast (show N ≠ 3 by omega)
    exact (mul_eq_zero.mp hp).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr hn3.symm) hF0)
  have hT : T = 0 := by
    apply contraction_injective hF hgrad
    funext i j
    simpa only [contractionCoefficients, trivectorCoefficient, zero_apply,
      map_zero, zero_mul, Finset.sum_const_zero] using hQ i j
  intro i j k
  have hr := euler_relation_of_divergence_lift F T B hskew hdegree hclosed i j k
  simp only [eulerWedge2, hQ, mul_zero, sub_zero, add_zero, zero_add] at hr
  have hNz : (N : CubicPolynomial N) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hEB : eulerWedge2 B i j k = 0 := by
    exact (mul_eq_zero.mp (by simpa only [nsmul_eq_mul, eulerWedge2] using hr)).resolve_left hNz
  simp [hT, trivectorCoefficient, hEB]

end NcCubic

namespace NcCubic
open MvPolynomial
open scoped BigOperators

/-- Coordinate Jacobiator, with the cyclic convention of the polynomial bracket. -/
def jacobiArray {N : ℕ} (q : Fin N → Fin N → CubicPolynomial N) (i j k : Fin N) :=
  ∑ r, (q i r * pderiv r (q j k) + q j r * pderiv r (q k i) +
    q k r * pderiv r (q i j))

/-- A divergence-free bivector has divergence-free Jacobiator. -/
theorem divergence3_jacobiArray {N : ℕ}
    (q : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, q j i = -q i j)
    (hdiv : ∀ j, divergence2 q j = 0) (i j : Fin N) :
    divergence3 (jacobiArray q) i j = 0 := by
  have hd (j r) : ∑ a, pderiv a (pderiv r (q a j)) = 0 := by
    simp_rw [pderiv_comm]
    rw [← map_sum]
    change pderiv r (divergence2 q j) = 0
    rw [hdiv, map_zero]
  have hA : (∑ a, ∑ r, pderiv a (q a r) * pderiv r (q i j)) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    change (∑ r, divergence2 q r * pderiv r (q i j)) = 0
    simp [hdiv]
  have hB : (∑ a, ∑ r, q a r * pderiv a (pderiv r (q i j))) = 0 := by
    apply CharZero.eq_neg_self_iff.mp
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    rw [hskew, pderiv_comm]
    ring
  have hD : (∑ a, ∑ r, q i r * pderiv a (pderiv r (q j a))) = 0 := by
    rw [Finset.sum_comm]
    have hja (a) : q j a = -q a j := hskew a j
    simp only [hja, map_neg]
    simp only [← Finset.mul_sum]
    simp only [Finset.sum_neg_distrib, hd, neg_zero, mul_zero, Finset.sum_const_zero]
  have hF : (∑ a, ∑ r, q j r * pderiv a (pderiv r (q a i))) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hd, mul_zero, Finset.sum_const_zero]
  have hCE : (∑ a, ∑ r, pderiv a (q i r) * pderiv r (q j a)) +
      (∑ a, ∑ r, pderiv a (q j r) * pderiv r (q a i)) = 0 := by
    rw [← neg_eq_iff_add_eq_zero]
    rw [Finset.sum_comm (f := fun a r => pderiv a (q j r) * pderiv r (q a i))]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    rw [hskew i r, map_neg]
    ring
  simp only [divergence3, jacobiArray, map_sum, map_add, pderiv_mul,
    Finset.sum_add_distrib]
  linear_combination hA + hB + hD + hF + hCE

end NcCubic

namespace NcCubic
open MvPolynomial
open scoped BigOperators

/-- The Jacobiator of a bracket with polynomial Casimir is horizontal for
that polynomial's differential. -/
theorem gradientContract3_jacobiArray {N : ℕ} (F : CubicPolynomial N)
    (q : Fin N → Fin N → CubicPolynomial N)
    (hskew : ∀ i j, q j i = -q i j)
    (hcasimir : ∀ j, ∑ a, q a j * pderiv a F = 0) (i j : Fin N) :
    gradientContract3 F (jacobiArray q) i j = 0 := by
  have hd (r j) : (∑ a, pderiv a F * pderiv r (q a j)) =
      -(∑ a, q a j * pderiv r (pderiv a F)) := by
    have hh := congrArg (pderiv r) (hcasimir j)
    simp only [map_sum, pderiv_mul, Finset.sum_add_distrib, map_zero] at hh
    have hc : (∑ a, pderiv a F * pderiv r (q a j)) =
        ∑ a, pderiv r (q a j) * pderiv a F := by
      apply Finset.sum_congr rfl; intro a _; ring
    rw [hc]
    exact eq_neg_of_add_eq_zero_left hh
  have hA : (∑ a, ∑ r, pderiv a F * (q a r * pderiv r (q i j))) = 0 := by
    rw [Finset.sum_comm]
    have hm (r) : (∑ a, pderiv a F * (q a r * pderiv r (q i j))) = 0 := by
      calc
        _ = (∑ a, q a r * pderiv a F) * pderiv r (q i j) := by
          simp only [Finset.sum_mul]; apply Finset.sum_congr rfl; intro a _; ring
        _ = 0 := by rw [hcasimir, zero_mul]
    simp [hm]
  have hB : (∑ a, ∑ r, pderiv a F * (q i r * pderiv r (q j a))) =
      ∑ r, ∑ a, q i r * q a j * pderiv r (pderiv a F) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    have hja (a) : q j a = -q a j := hskew a j
    simp only [hja, map_neg]
    calc
      _ = -q i r * ∑ a, pderiv a F * pderiv r (q a j) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      _ = _ := by rw [hd]; simp only [neg_mul_neg, Finset.mul_sum];
                  apply Finset.sum_congr rfl; intro a _; ring
  have hC : (∑ a, ∑ r, pderiv a F * (q j r * pderiv r (q a i))) =
      -(∑ r, ∑ a, q j r * q a i * pderiv r (pderiv a F)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    calc
      _ = q j r * ∑ a, pderiv a F * pderiv r (q a i) := by
        simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
      _ = _ := by rw [hd]; simp [Finset.mul_sum, mul_assoc]
  have hsym : (∑ r, ∑ a, q i r * q a j * pderiv r (pderiv a F)) =
      ∑ r, ∑ a, q j r * q a i * pderiv r (pderiv a F) := by
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    rw [hskew j a, hskew i r, pderiv_comm]
    ring
  simp only [gradientContract3, jacobiArray, mul_add, Finset.mul_sum,
    Finset.sum_add_distrib]
  rw [hA, hB, hC, hsym]
  ring

end NcCubic

namespace NcCubic
open MvPolynomial

/-- Proposition 2.4's algebraic conclusion from the geometric lift decomposition.
Existence of that lift is the separate projective-geometric obligation. -/
theorem contraction_jacobi_of_geometric_lift {N : ℕ} (hN : 5 ≤ N)
    (F : CubicPolynomial N) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F) (P : Trivector N)
    (hlift : ∃ (T : Trivector N) (B : Fin N → Fin N → CubicPolynomial N),
      (∀ i j, B j i = -B i j) ∧ (∀ i j, (B i j).IsHomogeneous 2) ∧
      ∀ i j k, jacobiArray (contractionCoefficients F P) i j k =
        F * C (trivectorCoefficient T i j k) + eulerWedge2 B i j k) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) := by
  obtain ⟨T, B, hskew, hdegree, hlift⟩ := hlift
  have hclosed : ∀ i j, divergence3 (fun a b c =>
      F * C (trivectorCoefficient T a b c) + eulerWedge2 B a b c) i j = 0 := by
    intro i j
    simp_rw [← hlift]
    exact divergence3_jacobiArray _ (contraction_skew F P)
      (divergence2_contraction F P) i j
  have hhorizontal : ∀ i j, gradientContract3 F (fun a b c =>
      F * C (trivectorCoefficient T a b c) + eulerWedge2 B a b c) i j = 0 := by
    intro i j
    simp_rw [← hlift]
    exact gradientContract3_jacobiArray F _ (contraction_skew F P)
      (contraction_gradient_zero F P) i j
  apply (JacobiCriterion.satisfiesJacobi_iff_coordinates _ (contraction_skew F P)).mpr
  intro i j k
  change jacobiArray (contractionCoefficients F P) i j k = 0
  rw [hlift]
  exact divergence_lift_vanishes hN F hF0 hF hgrad T B hskew hdegree
    hclosed hhorizontal i j k

end NcCubic
