/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Coordinates
public import StacksFrontier.RingTheory.Derivation.Localization
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.LocalizedPoisson
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}
variable (S : Submonoid (CubicPolynomial N)) (L : Type*) [CommRing L]
  [Algebra (CubicPolynomial N) L] [IsLocalization S L] [Algebra ℂ L]
  [IsScalarTower ℂ (CubicPolynomial N) L]

/-- The genuine extensions of the ambient coordinate derivations. -/
def localizedPderiv (i : Fin N) : Derivation ℂ L L := (pderiv i).localization S L

/-- The ambient polynomial bivector evaluated on arbitrary localized functions. -/
def bracket (q : Fin N → Fin N → CubicPolynomial N) (x y : L) : L :=
  ∑ i, ∑ j, algebraMap (CubicPolynomial N) L (q i j) * localizedPderiv S L i x * localizedPderiv S L j y

variable {S L}
@[simp] theorem bracket_algebraMap (q : Fin N → Fin N → CubicPolynomial N)
    (f g : CubicPolynomial N) :
    bracket S L q (algebraMap _ L f) (algebraMap _ L g) =
      algebraMap _ L (bracketFromCoefficients q f g) := by
  simp [bracket,localizedPderiv,bracketFromCoefficients]

@[simp] theorem bracket_zero_left (q : Fin N → Fin N → CubicPolynomial N) (y : L) :
    bracket S L q 0 y = 0 := by simp [bracket]
@[simp] theorem bracket_zero_right (q : Fin N → Fin N → CubicPolynomial N) (x : L) :
    bracket S L q x 0 = 0 := by simp [bracket]

theorem bracket_add_left (q : Fin N → Fin N → CubicPolynomial N) (x y z : L) :
    bracket S L q (x+y) z = bracket S L q x z + bracket S L q y z := by
  simp [bracket,mul_add,add_mul,Finset.sum_add_distrib]
theorem bracket_add_right (q : Fin N → Fin N → CubicPolynomial N) (x y z : L) :
    bracket S L q x (y+z) = bracket S L q x y + bracket S L q x z := by
  simp [bracket,mul_add,Finset.sum_add_distrib]

theorem bracket_skew (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, q j i = -q i j) (x y : L) : bracket S L q x y = -bracket S L q y x := by
  unfold bracket
  conv_lhs => rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hq,map_neg]
  ring

theorem bracket_mul_right (q : Fin N → Fin N → CubicPolynomial N) (x y z : L) :
    bracket S L q x (y*z) = y * bracket S L q x z + z * bracket S L q x y := by
  simp only [bracket,Derivation.leibniz,smul_eq_mul,mul_add,Finset.sum_add_distrib,
    Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem bracket_mul_left (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j, q j i = -q i j) (x y z : L) :
    bracket S L q (x*y) z = x * bracket S L q y z + y * bracket S L q x z := by
  rw [bracket_skew q hq (x*y) z,bracket_mul_right,
    bracket_skew q hq z x,bracket_skew q hq z y]
  ring

/-- Hamiltonian vector fields on the localization are genuine derivations. -/
def hamiltonian (q : Fin N → Fin N → CubicPolynomial N) (x : L) : Derivation ℂ L L :=
  ∑ i, ∑ j, (algebraMap (CubicPolynomial N) L (q i j) * localizedPderiv S L i x) •
    localizedPderiv S L j

@[simp] theorem hamiltonian_apply (q : Fin N → Fin N → CubicPolynomial N) (x y : L) :
    hamiltonian (S:=S) q x y = bracket S L q x y := by
  simp [hamiltonian,bracket,Derivation.smul_apply]

/-- Every polynomial Casimir remains a Casimir on all localized functions. -/
theorem bracket_polynomial_casimir (q : Fin N → Fin N → CubicPolynomial N)
    (F : CubicPolynomial N) (hF : ∀ g,bracketFromCoefficients q F g = 0) (x : L) :
    bracket S L q (algebraMap _ L F) x = 0 := by
  have hz : hamiltonian (S:=S) q (algebraMap _ L F) = 0 :=
    Derivation.eq_zero_of_isLocalization S L _ (by
      intro g
      rw [hamiltonian_apply,bracket_algebraMap,hF,map_zero])
  simpa only [hamiltonian_apply,Derivation.zero_apply] using
    congrArg (fun D : Derivation ℂ L L => D x) hz

/-- In particular the defining potential remains central after localization. -/
theorem bracket_potential (F : CubicPolynomial N) (P : Trivector N) (x : L) :
    bracket S L (contractionCoefficients F P) (algebraMap _ L F) x = 0 :=
  bracket_polynomial_casimir _ F (fun g => contraction_potential_casimir F g P) x

/-- The Jacobiator on the actual localization ring. -/
def jacobiator (q : Fin N → Fin N → CubicPolynomial N) (x y z : L) : L :=
  bracket S L q x (bracket S L q y z) + bracket S L q y (bracket S L q z x) +
    bracket S L q z (bracket S L q x y)

theorem jacobiator_cyclic (q : Fin N → Fin N → CubicPolynomial N) (x y z : L) :
    jacobiator (S:=S) q x y z = jacobiator (S:=S) q y z x := by unfold jacobiator; ring

theorem jacobiator_add (q : Fin N → Fin N → CubicPolynomial N) (x y z w : L) :
    jacobiator (S:=S) q (x+y) z w =
      jacobiator (S:=S) q x z w + jacobiator (S:=S) q y z w := by
  simp only [jacobiator,bracket_add_left,bracket_add_right]
  ring

theorem jacobiator_mul (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (x y z w : L) :
    jacobiator (S:=S) q (x*y) z w =
      x*jacobiator (S:=S) q y z w + y*jacobiator (S:=S) q x z w := by
  simp only [jacobiator,bracket_mul_left q hq,bracket_mul_right,
    bracket_add_right]
  rw [bracket_skew q hq w x,bracket_skew q hq y z,bracket_skew q hq z x]
  ring

/-- For a skew biderivation the Jacobiator is an honest derivation in its
first variable; localization uniqueness can therefore test it on the base. -/
def jacobiDerivation (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (y z : L) : Derivation ℤ L L :=
  Derivation.mk'
    ({toFun := fun x => jacobiator (S:=S) q x y z
      map_zero' := by simp [jacobiator]
      map_add' := fun x w => jacobiator_add q x w y z} : L →+ L).toIntLinearMap
    (by
      intro x w
      change jacobiator (S:=S) q (x*w) y z =
        x • jacobiator (S:=S) q w y z + w • jacobiator (S:=S) q x y z
      simpa only [smul_eq_mul] using jacobiator_mul q hq x w y z)

/-- Polynomial Jacobi holds on every localized function, not merely on
images of polynomials or on chart generators. -/
theorem bracket_jacobi (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j)
    (hJac : ∀ f g h : CubicPolynomial N,
      bracketFromCoefficients q f (bracketFromCoefficients q g h) +
      bracketFromCoefficients q g (bracketFromCoefficients q h f) +
      bracketFromCoefficients q h (bracketFromCoefficients q f g) = 0)
    (x y z : L) : jacobiator (S:=S) q x y z = 0 := by
  have extend (y z : L)
      (hb : ∀ f : CubicPolynomial N, jacobiator (S:=S) q (algebraMap _ L f) y z = 0) :
      ∀ x : L,jacobiator (S:=S) q x y z = 0 := by
    have hz : jacobiDerivation q hq y z = 0 :=
      Derivation.eq_zero_of_isLocalization S L (jacobiDerivation (S:=S) q hq y z) (by
        intro a
        change jacobiator (S:=S) q (algebraMap _ L a) y z = 0
        exact hb a)
    intro x
    exact congrArg (fun D : Derivation ℤ L L => D x) hz
  apply extend y z
  intro f
  rw [jacobiator_cyclic]
  apply extend z (algebraMap _ L f)
  intro g
  rw [jacobiator_cyclic]
  apply extend (algebraMap _ L f) (algebraMap _ L g)
  intro h
  rw [jacobiator_cyclic]
  simp only [jacobiator,bracket_algebraMap, ← map_add, hJac, map_zero]
/-- The localized bracket is complex-linear in each slot. -/
theorem bracket_smul_right (q : Fin N → Fin N → CubicPolynomial N)
    (c : ℂ) (x y : L) : bracket S L q x (c • y) = c • bracket S L q x y := by
  simp [bracket, Finset.smul_sum]

theorem bracket_smul_left (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (c : ℂ) (x y : L) :
    bracket S L q (c • x) y = c • bracket S L q x y := by
  rw [bracket_skew q hq,bracket_smul_right,bracket_skew q hq x y]
  simp

theorem bracket_neg_right (q : Fin N → Fin N → CubicPolynomial N) (x y : L) :
    bracket S L q x (-y) = -bracket S L q x y := by
  simp [bracket,mul_neg,Finset.sum_neg_distrib]

theorem bracket_self (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j) (x : L) : bracket S L q x x = 0 := by
  have hs := bracket_skew (S:=S) q hq x x
  have ht : (2 : ℂ) • bracket S L q x x = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hs
  have h := congrArg (fun v : L => (2 : ℂ)⁻¹ • v) ht
  simpa [smul_smul] using h

/-- Every localization comparison map intertwines the actual coordinate
partial derivatives. -/
theorem localizedPderiv_natural {T : Submonoid (CubicPolynomial N)}
    {M : Type*} [CommRing M] [Algebra (CubicPolynomial N) M] [IsLocalization T M]
    [Algebra ℂ M] [IsScalarTower ℂ (CubicPolynomial N) M]
    (g : L →ₐ[CubicPolynomial N] M) (i : Fin N) (x : L) :
    g (localizedPderiv S L i x) = localizedPderiv T M i (g x) := by
  exact Stacks.DerivationExtension.algHom_locDeriv (S:=S) (T:=T)
    ((pderiv i : Derivation ℂ (CubicPolynomial N) (CubicPolynomial N)).restrictScalars ℤ)
    L M g x

/-- Naturality holds on all localized functions and actual overlap maps. -/
theorem bracket_natural (q : Fin N → Fin N → CubicPolynomial N)
    {T : Submonoid (CubicPolynomial N)}
    {M : Type*} [CommRing M] [Algebra (CubicPolynomial N) M] [IsLocalization T M]
    [Algebra ℂ M] [IsScalarTower ℂ (CubicPolynomial N) M]
    (g : L →ₐ[CubicPolynomial N] M) (x y : L) :
    g (bracket S L q x y) = bracket T M q (g x) (g y) := by
  simp only [bracket,map_sum,map_mul,AlgHom.commutes,
    ]
  simp_rw [localizedPderiv_natural (S:=S) (T:=T) g]

/-- The localized Poisson bracket supplies an actual Lie ring on the same
commutative ring, while retaining the proven product Leibniz rule. -/
@[instance_reducible]
def localizedLieRing (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j)
    (hJac : ∀ f g h : CubicPolynomial N,
      bracketFromCoefficients q f (bracketFromCoefficients q g h) +
      bracketFromCoefficients q g (bracketFromCoefficients q h f) +
      bracketFromCoefficients q h (bracketFromCoefficients q f g) = 0) : LieRing L where
  toAddCommGroup := inferInstance
  bracket := bracket S L q
  add_lie := bracket_add_left q
  lie_add := bracket_add_right q
  lie_self := bracket_self q hq
  leibniz_lie := by
    intro x y z
    have hj := bracket_jacobi (S:=S) q hq hJac x y z
    unfold jacobiator at hj
    rw [bracket_skew q hq z x,bracket_neg_right,
      bracket_skew q hq z (bracket S L q x y)] at hj
    linear_combination hj

/-- The localized Lie bracket has the original complex scalar action. -/
@[instance_reducible]
def localizedLieAlgebra (q : Fin N → Fin N → CubicPolynomial N)
    (hq : ∀ i j,q j i = -q i j)
    (hJac : ∀ f g h : CubicPolynomial N,
      bracketFromCoefficients q f (bracketFromCoefficients q g h) +
      bracketFromCoefficients q g (bracketFromCoefficients q h f) +
      bracketFromCoefficients q h (bracketFromCoefficients q f g) = 0) :
    @LieAlgebra ℂ L inferInstance (localizedLieRing (S:=S) (L:=L) q hq hJac) := by
  letI := localizedLieRing (S:=S) (L:=L) q hq hJac
  exact {toModule := inferInstance,lie_smul := fun c x y => bracket_smul_right q c x y}
end NcCubic.Geometry.LocalizedPoisson
