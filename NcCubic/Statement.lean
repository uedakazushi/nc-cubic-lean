/- The affine, coordinate-level target of Theorem 1.1(3).

This file DEFINES the target proposition. It does not prove it. The projective
geometric bridge remains a separate obligation in blueprint/README.md.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Basic.Complex.Basic

@[expose] public section

noncomputable section

namespace NcCubic

open MvPolynomial
open scoped BigOperators

abbrev CoordinateSpace (N : ℕ) := Fin N → ℂ
abbrev CubicPolynomial (N : ℕ) := MvPolynomial (Fin N) ℂ
abbrev Covector (N : ℕ) := Module.Dual ℂ (CoordinateSpace N)

/-- A contravariant alternating tensor, realized on the dual space. -/
abbrev Trivector (N : ℕ) := AlternatingMap ℂ (Covector N) ℂ (Fin 3)

def coordinateCovector {N : ℕ} (i : Fin N) : Covector N where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def trivectorCoefficient {N : ℕ} (P : Trivector N) (i j a : Fin N) : ℂ :=
  P ![coordinateCovector i, coordinateCovector j, coordinateCovector a]

/-- The standard homogeneous quadratic representative q = i_(dF) P. -/
def contractionCoefficients {N : ℕ} (F : CubicPolynomial N) (P : Trivector N)
    (i j : Fin N) : CubicPolynomial N :=
  ∑ a, C (trivectorCoefficient P i j a) * pderiv a F

def bracketFromCoefficients {N : ℕ} (q : Fin N → Fin N → CubicPolynomial N)
    (f g : CubicPolynomial N) : CubicPolynomial N :=
  ∑ i, ∑ j, q i j * pderiv i f * pderiv j g

/-- Jacobi on all polynomials, rather than only on coordinate generators. -/
def SatisfiesJacobi {N : ℕ}
    (bracket : CubicPolynomial N → CubicPolynomial N → CubicPolynomial N) : Prop :=
  ∀ f g h, bracket f (bracket g h) + bracket g (bracket h f) +
    bracket h (bracket f g) = 0

/-- Together with homogeneity and characteristic zero, this is the gradient
criterion to be connected to smoothness of the projective hypersurface. -/
def HasIsolatedGradientZero {N : ℕ} (F : CubicPolynomial N) : Prop :=
  ∀ x : CoordinateSpace N, (∀ i, eval x (pderiv i F) = 0) → x = 0

abbrev BlockIndex (k m : ℕ) := (Fin k × Fin 3) ⊕ Fin m

/-- Substitution z_i = sum_j (b_j)_i y_j for a new vector-space basis b. -/
def polynomialInBasis {N k m : ℕ} (F : CubicPolynomial N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) :
    MvPolynomial (BlockIndex k m) ℂ :=
  aeval (fun i : Fin N => ∑ j : BlockIndex k m, C ((b j) i) * X j) F

def blockVariable {k m : ℕ} (s : Fin k) : Fin 3 ⊕ Fin m → BlockIndex k m :=
  Sum.elim (fun i => Sum.inl (s, i)) Sum.inr

/-- The equation for P is evaluated on arbitrary covectors, so no coordinate
test or unstated tensor-extensionality lemma is smuggled into the target. -/
def HasBlockTrivector {N k m : ℕ} (P : Trivector N)
    (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N)) : Prop :=
  ∀ α : Fin 3 → Covector N,
    P α = ∑ s : Fin k,
      Matrix.det (fun i j : Fin 3 => α i (b (Sum.inl (s, j))))

def HasBlockNormalForm {N : ℕ} (F : CubicPolynomial N) (P : Trivector N) : Prop :=
  ∃ (k m : ℕ), 1 ≤ k ∧ N = 3 * k + m ∧
    ∃ (b : Module.Basis (BlockIndex k m) ℂ (CoordinateSpace N))
      (f : Fin k → MvPolynomial (Fin 3 ⊕ Fin m) ℂ),
      (∀ s, (f s).IsHomogeneous 3) ∧ HasBlockTrivector P b ∧
      polynomialInBasis F b = ∑ s, rename (blockVariable s) (f s)

/-- OPEN TARGET, not a theorem. Its eventual proof must be named
`NcCubic.theorem113_affine`. The full geometric theorem additionally requires
the representation and lifting results in Section 2 of the source paper. -/
def AffineClassificationStatement : Prop :=
  ∀ (N : ℕ), 5 ≤ N → ∀ (F : CubicPolynomial N) (P : Trivector N),
    F ≠ 0 → F.IsHomogeneous 3 → HasIsolatedGradientZero F → P ≠ 0 →
    (SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) ↔
      HasBlockNormalForm F P)

end NcCubic
