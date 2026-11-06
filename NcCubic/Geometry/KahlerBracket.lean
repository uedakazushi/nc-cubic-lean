module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Tactic.FinCases
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open scoped KaehlerDifferential
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
def rightHamiltonian
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y) (x : A) : Derivation R A A :=
  Derivation.mk' (b x) (hr x)
def doubleHamiltonian
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z) :
    Derivation R A (Derivation R A A) :=
  Derivation.mk' {
    toFun := rightHamiltonian b hr
    map_add' := fun x y => by ext z; exact LinearMap.congr_fun (b.map_add x y) z
    map_smul' := fun r x => by ext z; exact LinearMap.congr_fun (b.map_smul r x) z
  } (by intro x y; ext z; exact hl x y z)
/-- The actual Kähler pairing canonically represented by a biderivation. -/
def kahlerBracket
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z) :
    KaehlerDifferential R A →ₗ[A] KaehlerDifferential R A →ₗ[A] A :=
  (KaehlerDifferential.linearMapEquivDerivation (M := A) R A).symm.toLinearMap.comp
    (doubleHamiltonian b hr hl).liftKaehlerDifferential
@[simp] theorem kahlerBracket_d_d
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z) (x y : A) :
    kahlerBracket b hr hl (KaehlerDifferential.D R A x) (KaehlerDifferential.D R A y) =
      b x y := by
  change (((doubleHamiltonian b hr hl).liftKaehlerDifferential
    (KaehlerDifferential.D R A x)).liftKaehlerDifferential (KaehlerDifferential.D R A y)) = _
  rw [Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]
  rfl
theorem kahlerBilinear_ext
    {B C : KaehlerDifferential R A →ₗ[A] KaehlerDifferential R A →ₗ[A] A}
    (h : ∀ x y, B (KaehlerDifferential.D R A x) (KaehlerDifferential.D R A y) =
      C (KaehlerDifferential.D R A x) (KaehlerDifferential.D R A y)) : B = C := by
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro x
  apply Derivation.liftKaehlerDifferential_unique
  apply Derivation.ext
  intro y
  exact h x y

theorem kahlerBracket_skew
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x)
    (x y : KaehlerDifferential R A) : kahlerBracket b hr hl x y = -kahlerBracket b hr hl y x := by
  have he : kahlerBracket b hr hl = -(kahlerBracket b hr hl).flip := by
    apply kahlerBilinear_ext
    intro a c
    simpa only [LinearMap.neg_apply, LinearMap.flip_apply, kahlerBracket_d_d] using hskew a c
  exact congrArg (fun f => f x y) he

theorem kahlerBracket_alternating
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x) (hdiag : ∀x, b x x = 0)
    (x : KaehlerDifferential R A) : kahlerBracket b hr hl x x = 0 := by
  have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; simpa using hdiag a
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    rw [kahlerBracket_skew b hr hl hskew x y]
    simp
  | smul a x _ hx => simp [map_smul, LinearMap.smul_apply, hx]

def kahlerBracketAlternating
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x) (hdiag : ∀x, b x x = 0) :
    AlternatingMap A (KaehlerDifferential R A) A (Fin 2) where
  toFun v := kahlerBracket b hr hl (v 0) (v 1)
  map_update_add' v i x y := by fin_cases i <;> simp
  map_update_smul' v i c x := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij; rw [hij]; exact kahlerBracket_alternating b hr hl hskew hdiag _
    · change v 1 = v 0 at hij; rw [← hij]; exact kahlerBracket_alternating b hr hl hskew hdiag _
    · exact (hne rfl).elim

/-- A genuine linear form on the exterior square of Kähler differentials. -/
def kahlerExteriorBracket
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x) (hdiag : ∀x, b x x = 0) :
    ⋀[A]^2 (KaehlerDifferential R A) →ₗ[A] A :=
  exteriorPower.alternatingMapLinearEquiv (kahlerBracketAlternating b hr hl hskew hdiag)

@[simp] theorem kahlerExteriorBracket_d_wedge_d
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x) (hdiag : ∀x, b x x = 0) (x y : A) :
    kahlerExteriorBracket b hr hl hskew hdiag
      (exteriorPower.ιMulti A 2 ![KaehlerDifferential.D R A x, KaehlerDifferential.D R A y]) =
      b x y := by
  simp [kahlerExteriorBracket, kahlerBracketAlternating]

/-- For a finite free cotangent module the bracket is an actual tangent bivector. -/
def kahlerBivector [Module.Free A (KaehlerDifferential R A)]
    [Module.Finite A (KaehlerDifferential R A)]
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x) (hdiag : ∀x, b x x = 0) :
    ⋀[A]^2 (Module.Dual A (KaehlerDifferential R A)) :=
  (LinearEquiv.ofBijective (exteriorPower.pairingDual A (KaehlerDifferential R A) 2)
    (exteriorPower.bijective_pairingDual A (KaehlerDifferential R A) 2)).symm
    (kahlerExteriorBracket b hr hl hskew hdiag)
@[simp] theorem kahlerBivector_pairing [Module.Free A (KaehlerDifferential R A)]
    [Module.Finite A (KaehlerDifferential R A)]
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x) (hdiag : ∀x, b x x = 0) :
    exteriorPower.pairingDual A (KaehlerDifferential R A) 2
      (kahlerBivector b hr hl hskew hdiag) = kahlerExteriorBracket b hr hl hskew hdiag := by
  exact (LinearEquiv.ofBijective (exteriorPower.pairingDual A (KaehlerDifferential R A) 2)
    (exteriorPower.bijective_pairingDual A (KaehlerDifferential R A) 2)).apply_symm_apply _

@[simp] theorem kahlerBivector_d_wedge_d [Module.Free A (KaehlerDifferential R A)]
    [Module.Finite A (KaehlerDifferential R A)]
    (b : A →ₗ[R] A →ₗ[R] A)
    (hr : ∀ x y z, b x (y*z) = y*b x z + z*b x y)
    (hl : ∀ x y z, b (x*y) z = x*b y z + y*b x z)
    (hskew : ∀x y, b x y = -b y x) (hdiag : ∀x, b x x = 0) (x y : A) :
    exteriorPower.pairingDual A (KaehlerDifferential R A) 2
      (kahlerBivector b hr hl hskew hdiag)
      (exteriorPower.ιMulti A 2 ![KaehlerDifferential.D R A x, KaehlerDifferential.D R A y]) =
      b x y := by
  rw [kahlerBivector_pairing, kahlerExteriorBracket_d_wedge_d]

end NcCubic.Geometry
