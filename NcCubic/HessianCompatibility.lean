/- Covector-level compatibility and its coordinate criterion. -/
module
public import NcCubic.JacobiCriterion
public import NcCubic.CubicDifferential
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Multilinear.Basis
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

@[expose] public section
noncomputable section
namespace NcCubic.HessianCompatibility
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- Contract a trivector with two covectors, using finite-dimensional biduality. -/
def contraction (P : Trivector N) :
    Covector N →ₗ[ℂ] Covector N →ₗ[ℂ] CoordinateSpace N where
  toFun α := {
    toFun := fun β a => P ![α, β, coordinateCovector a]
    map_add' := by
      intro β γ
      funext a
      change (P.toMultilinearMap.curryLeft α).curryLeft (β + γ) ![coordinateCovector a] = _
      rw [map_add]
      rfl
    map_smul' := by
      intro c β
      funext a
      change (P.toMultilinearMap.curryLeft α).curryLeft (c • β) ![coordinateCovector a] = _
      rw [map_smul]
      rfl }
  map_add' := by
    intro α β
    ext γ a
    change P.toMultilinearMap.curryLeft (α + β) ![γ, coordinateCovector a] = _
    rw [map_add]
    rfl
  map_smul' := by
    intro c α
    ext β a
    change P.toMultilinearMap.curryLeft (c • α) ![β, coordinateCovector a] = _
    rw [map_smul]
    rfl

/-- This coordinate construction is the intrinsic contraction characterized by biduality. -/
theorem contraction_eval (P : Trivector N) (α β γ : Covector N) :
    γ (contraction P α β) = P ![α, β, γ] := by
  let f : Covector N →ₗ[ℂ] ℂ := {
    toFun := fun γ => γ (contraction P α β)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have heq : f = P.toMultilinearMap.curryRight ![α, β] := by
    apply (Pi.basisFun ℂ (Fin N)).dualBasis.ext
    intro i
    have hv : (Pi.basisFun ℂ (Fin N)).dualBasis i = coordinateCovector i := by
      ext x
      simp [coordinateCovector]
    rw [hv]
    simp only [MultilinearMap.curryRight_apply, Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty]
    rfl
  have h := congrArg (fun g : Covector N →ₗ[ℂ] ℂ => g γ) heq
  simpa only [f, LinearMap.coe_mk, AddHom.coe_mk, MultilinearMap.curryRight_apply,
    Matrix.Fin.snoc_vecCons, Matrix.Fin.snoc_vecEmpty, AlternatingMap.coe_multilinearMap] using h

/-- The quadrilinear expression in paper equation (3.1). -/
def compatibility (P : Trivector N) (H : LinearMap.BilinForm ℂ (CoordinateSpace N)) :
    MultilinearMap ℂ (fun _ : Fin 4 => Covector N) ℂ where
  toFun α := H (contraction P (α 0) (α 1)) (contraction P (α 2) (α 3)) +
    H (contraction P (α 1) (α 2)) (contraction P (α 0) (α 3)) +
    H (contraction P (α 2) (α 0)) (contraction P (α 1) (α 3))
  map_update_add' := by
    intro dec α i x y
    have hd : dec = (fun (a b : Fin 4) => decidable_of_iff (a.val = b.val) Fin.ext_iff.symm) := Subsingleton.elim _ _
    subst dec
    fin_cases i <;>
      simp [map_add, LinearMap.add_apply] <;> ring
  map_update_smul' := by
    intro dec α i c x
    have hd : dec = (fun (a b : Fin 4) => decidable_of_iff (a.val = b.val) Fin.ext_iff.symm) := Subsingleton.elim _ _
    subst dec
    fin_cases i <;>
      simp [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_add]

/-- Every covector quadruple satisfies the compatibility relation. -/
def Compatible (P : Trivector N) (H : LinearMap.BilinForm ℂ (CoordinateSpace N)) : Prop :=
  ∀ α, compatibility P H α = 0

/-- Covector-level compatibility can be checked on coordinate covectors. -/
theorem compatible_iff_coordinates (P : Trivector N)
    (H : LinearMap.BilinForm ℂ (CoordinateSpace N)) :
    Compatible P H ↔ ∀ i j k a,
      compatibility P H ![coordinateCovector i, coordinateCovector j,
        coordinateCovector k, coordinateCovector a] = 0 := by
  constructor
  · intro h i j k a
    exact h _
  · intro h
    have heq : compatibility P H = 0 := by
      apply Module.Basis.ext_multilinear (fun _ : Fin 4 => (Pi.basisFun ℂ (Fin N)).dualBasis)
      intro v
      have hv (i : Fin N) : (Pi.basisFun ℂ (Fin N)).dualBasis i = coordinateCovector i := by
        ext x
        simp [coordinateCovector]
      simp only [hv]
      have ht : (fun i : Fin 4 => coordinateCovector (v i)) =
          ![coordinateCovector (v 0), coordinateCovector (v 1),
            coordinateCovector (v 2), coordinateCovector (v 3)] := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact h _ _ _ _
    intro α
    rw [heq]
    rfl

/-- Evaluation of a bilinear form by its matrix in the standard basis. -/
theorem bilinear_coordinates (H : LinearMap.BilinForm ℂ (CoordinateSpace N))
    (v w : CoordinateSpace N) :
    H v w = ∑ r, ∑ b, v r * w b * H (Pi.single r 1) (Pi.single b 1) := by
  have expand (v : CoordinateSpace N) : v = ∑ r, v r • Pi.single r (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [expand v, expand w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem bilinear_contraction_coordinates (P : Trivector N)
    (H : LinearMap.BilinForm ℂ (CoordinateSpace N)) (i j k a : Fin N) :
    H (contraction P (coordinateCovector i) (coordinateCovector j))
      (contraction P (coordinateCovector k) (coordinateCovector a)) =
    ∑ r, ∑ b, trivectorCoefficient P i j r * trivectorCoefficient P k a b *
      H (Pi.single r 1) (Pi.single b 1) := by
  rw [bilinear_coordinates]
  rfl

/-- The coordinate matrix formula for the covector-level compatibility relation. -/
theorem compatibility_coordinates (P : Trivector N)
    (H : LinearMap.BilinForm ℂ (CoordinateSpace N)) (i j k a : Fin N) :
    compatibility P H ![coordinateCovector i, coordinateCovector j,
      coordinateCovector k, coordinateCovector a] =
    ∑ r, ∑ b,
      (trivectorCoefficient P i j r * trivectorCoefficient P k a b +
        trivectorCoefficient P j k r * trivectorCoefficient P i a b +
        trivectorCoefficient P k i r * trivectorCoefficient P j a b) *
          H (Pi.single r 1) (Pi.single b 1) := by
  change H (contraction P (coordinateCovector i) (coordinateCovector j))
      (contraction P (coordinateCovector k) (coordinateCovector a)) +
    H (contraction P (coordinateCovector j) (coordinateCovector k))
      (contraction P (coordinateCovector i) (coordinateCovector a)) +
    H (contraction P (coordinateCovector k) (coordinateCovector i))
      (contraction P (coordinateCovector j) (coordinateCovector a)) = _
  simp only [bilinear_contraction_coordinates, add_mul, Finset.sum_add_distrib]

/-- Matrix entries of the actual Hessian bilinear form. -/
theorem hessianForm_basis (F : CubicPolynomial N) (p : CoordinateSpace N) (r b : Fin N) :
    CubicDifferential.hessianForm F p (Pi.single r 1) (Pi.single b 1) =
      eval p (pderiv r (pderiv b F)) := by
  simp [CubicDifferential.hessianForm, CubicDifferential.hessian, Pi.single_apply,
    ite_mul]

/-- Polynomial compatibility coefficients are the matrix evaluations of K(P). -/
theorem hessian_compatibility_coordinates (F : CubicPolynomial N) (P : Trivector N)
    (p : CoordinateSpace N) (i j k a : Fin N) :
    compatibility P (CubicDifferential.hessianForm F p)
      ![coordinateCovector i, coordinateCovector j, coordinateCovector k, coordinateCovector a] =
    eval p (JacobiCriterion.compatibilityCoefficient P
      (fun r b => pderiv r (pderiv b F)) i j k a) := by
  rw [compatibility_coordinates]
  simp [JacobiCriterion.compatibilityCoefficient, hessianForm_basis]

/-- Quantification over all points and covectors is equivalent to polynomial matrix equations. -/
theorem all_hessians_compatible_iff (F : CubicPolynomial N) (P : Trivector N) :
    (∀ p, Compatible P (CubicDifferential.hessianForm F p)) ↔
    ∀ i j k a, JacobiCriterion.compatibilityCoefficient P
      (fun r b => pderiv r (pderiv b F)) i j k a = 0 := by
  constructor
  · intro h i j k a
    apply MvPolynomial.funext
    intro p
    simpa only [map_zero] using
      (hessian_compatibility_coordinates F P p i j k a).symm.trans
        ((compatible_iff_coordinates P _).1 (h p) i j k a)
  · intro h p
    apply (compatible_iff_coordinates P _).2
    intro i j k a
    rw [hessian_compatibility_coordinates, h, map_zero]

/-- Every compatible Hessian gives Jacobi, without smoothness or degree hypotheses. -/
theorem jacobi_of_all_hessians_compatible (F : CubicPolynomial N) (P : Trivector N)
    (h : ∀ p, Compatible P (CubicDifferential.hessianForm F p)) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) :=
  JacobiCriterion.jacobi_of_compatibility F P ((all_hessians_compatible_iff F P).1 h)

/-- The exact geometric-looking Hessian criterion, conditional only on the explicit
remaining low-degree syzygy theorem. No classification conclusion is assumed. -/
theorem jacobi_iff_all_hessians_compatible_of_no_linear_syzygy
    (F : CubicPolynomial N) (P : Trivector N) (hF : F.IsHomogeneous 3)
    (hsyzygy : ∀ A : Fin N → CubicPolynomial N,
      (∀ a, (A a).IsHomogeneous 1) → (∑ a, pderiv a F * A a) = 0 → ∀ a, A a = 0) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) ↔
      ∀ p, Compatible P (CubicDifferential.hessianForm F p) := by
  rw [all_hessians_compatible_iff]
  exact JacobiCriterion.jacobi_iff_compatibility_of_no_linear_syzygy F P hF hsyzygy

/-- The space K(P): compatible symmetric complex bilinear forms. -/
def compatibleForms (P : Trivector N) :
    Submodule ℂ (LinearMap.BilinForm ℂ (CoordinateSpace N)) where
  carrier := {H | Compatible P H ∧ ∀ v w, H v w = H w v}
  zero_mem' := by
    constructor
    · intro α
      simp [compatibility]
    · intros; rfl
  add_mem' := by
    intro H G hH hG
    constructor
    · intro α
      have hh := hH.1 α
      have hg := hG.1 α
      dsimp only [compatibility] at hh hg ⊢
      simp only [MultilinearMap.coe_mk, LinearMap.add_apply] at hh hg ⊢
      linear_combination hh + hg
    · intro v w
      simp only [LinearMap.add_apply, hH.2 v w, hG.2 v w]
  smul_mem' := by
    intro c H hH
    constructor
    · intro α
      have hh := hH.1 α
      dsimp only [compatibility] at hh ⊢
      simp only [MultilinearMap.coe_mk, LinearMap.smul_apply, smul_eq_mul] at hh ⊢
      linear_combination c * hh
    · intro v w
      simp only [LinearMap.smul_apply, hH.2 v w]

theorem compatibleForms_isSymm (P : Trivector N)
    (H : LinearMap.BilinForm ℂ (CoordinateSpace N)) (hH : H ∈ compatibleForms P) :
    H.IsSymm := ⟨hH.2⟩

theorem hessianForm_mem_compatibleForms (F : CubicPolynomial N) (P : Trivector N)
    (p : CoordinateSpace N) (h : Compatible P (CubicDifferential.hessianForm F p)) :
    CubicDifferential.hessianForm F p ∈ compatibleForms P :=
  ⟨h, CubicDifferential.hessianForm_symm F p⟩

/-- Smoothness in the explicit gradient model makes K(P) basepoint-free
as soon as the Hessians are compatible. -/
theorem compatibleForms_basepoint_free (F : CubicPolynomial N) (P : Trivector N)
    (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (h : ∀ p, Compatible P (CubicDifferential.hessianForm F p))
    (w : CoordinateSpace N) (hw : w ≠ 0) :
    ∃ H ∈ compatibleForms P, H w w ≠ 0 := by
  obtain ⟨p, hp⟩ := CubicDifferential.hessian_basepoint_free hF hgrad w hw
  exact ⟨CubicDifferential.hessianForm F p,
    hessianForm_mem_compatibleForms F P p (h p), hp⟩

end NcCubic.HessianCompatibility
