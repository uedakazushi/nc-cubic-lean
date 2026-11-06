module
public import NcCubic.Coordinates
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial
open scoped BigOperators
variable {N : ℕ}

/-- The actual affine coordinate ring of the cubic cone. -/
abbrev ConeCoordinateRing (F : CubicPolynomial N) :=
  CubicPolynomial N ⧸ Ideal.span {F}

private theorem bracket_sub_left (q : Fin N → Fin N → CubicPolynomial N) (a b c : CubicPolynomial N) :
    bracketFromCoefficients q (a - b) c = bracketFromCoefficients q a c - bracketFromCoefficients q b c := by
  simp [bracketFromCoefficients, map_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]

private theorem bracket_sub_right (q : Fin N → Fin N → CubicPolynomial N) (a b c : CubicPolynomial N) :
    bracketFromCoefficients q a (b - c) = bracketFromCoefficients q a b - bracketFromCoefficients q a c := by
  simp [bracketFromCoefficients, map_sub, mul_sub, Finset.sum_sub_distrib]

private theorem bracket_leibniz_left (q : Fin N → Fin N → CubicPolynomial N) (a b c : CubicPolynomial N) :
    bracketFromCoefficients q (a * b) c = b * bracketFromCoefficients q a c + a * bracketFromCoefficients q b c := by
  simp only [bracketFromCoefficients, pderiv_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

/-- Casimir contraction preserves the defining ideal in the first entry. -/
theorem contraction_bracket_mem_ideal_left (F : CubicPolynomial N) (P : Trivector N)
    (a b : CubicPolynomial N) (ha : a ∈ Ideal.span {F}) :
    bracketFromCoefficients (contractionCoefficients F P) a b ∈ Ideal.span {F} := by
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton.mp ha
  rw [hu, bracket_leibniz_left, contraction_potential_casimir]
  simp only [mul_zero, zero_add]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right F _)

/-- The same defining ideal is preserved in the second entry. -/
theorem contraction_bracket_mem_ideal_right (F : CubicPolynomial N) (P : Trivector N)
    (a b : CubicPolynomial N) (hb : b ∈ Ideal.span {F}) :
    bracketFromCoefficients (contractionCoefficients F P) a b ∈ Ideal.span {F} := by
  rw [bracket_skew _ (contraction_skew F P)]
  exact (Ideal.span {F}).neg_mem (contraction_bracket_mem_ideal_left F P b a hb)

theorem contraction_bracket_quotient_congr (F : CubicPolynomial N) (P : Trivector N)
    (a b a' b' : CubicPolynomial N)
    (ha : Ideal.Quotient.mk (Ideal.span {F}) a = Ideal.Quotient.mk (Ideal.span {F}) a')
    (hb : Ideal.Quotient.mk (Ideal.span {F}) b = Ideal.Quotient.mk (Ideal.span {F}) b') :
    Ideal.Quotient.mk (Ideal.span {F}) (bracketFromCoefficients (contractionCoefficients F P) a b) =
      Ideal.Quotient.mk (Ideal.span {F}) (bracketFromCoefficients (contractionCoefficients F P) a' b') := by
  have hleft : Ideal.Quotient.mk (Ideal.span {F}) (bracketFromCoefficients (contractionCoefficients F P) a b) =
      Ideal.Quotient.mk (Ideal.span {F}) (bracketFromCoefficients (contractionCoefficients F P) a' b) := by
    apply Ideal.Quotient.eq.mpr
    rw [← bracket_sub_left]
    exact contraction_bracket_mem_ideal_left F P _ _ (Ideal.Quotient.eq.mp ha)
  have hright : Ideal.Quotient.mk (Ideal.span {F}) (bracketFromCoefficients (contractionCoefficients F P) a' b) =
      Ideal.Quotient.mk (Ideal.span {F}) (bracketFromCoefficients (contractionCoefficients F P) a' b') := by
    apply Ideal.Quotient.eq.mpr
    rw [← bracket_sub_right]
    exact contraction_bracket_mem_ideal_right F P _ _ (Ideal.Quotient.eq.mp hb)
  exact hleft.trans hright

/-- The contraction bracket descends to the actual affine cone quotient ring. -/
def coneBracket (F : CubicPolynomial N) (P : Trivector N)
    (a b : ConeCoordinateRing F) : ConeCoordinateRing F :=
  Quotient.liftOn₂ a b
    (fun x y => Ideal.Quotient.mk (Ideal.span {F})
      (bracketFromCoefficients (contractionCoefficients F P) x y))
    (fun x y x' y' hx hy => contraction_bracket_quotient_congr F P x y x' y'
      (Quotient.sound hx) (Quotient.sound hy))

@[simp] theorem coneBracket_mk (F : CubicPolynomial N) (P : Trivector N)
    (a b : CubicPolynomial N) :
    coneBracket F P (Ideal.Quotient.mk (Ideal.span {F}) a) (Ideal.Quotient.mk (Ideal.span {F}) b) =
      Ideal.Quotient.mk (Ideal.span {F}) (bracketFromCoefficients (contractionCoefficients F P) a b) := rfl

theorem coneBracket_skew (F : CubicPolynomial N) (P : Trivector N)
    (a b : ConeCoordinateRing F) : coneBracket F P a b = -coneBracket F P b a := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  have he := congrArg (Ideal.Quotient.mk (Ideal.span {F}))
    (bracket_skew _ (contraction_skew F P) y x)
  simpa only [map_neg, coneBracket_mk] using he

theorem coneBracket_add_right (F : CubicPolynomial N) (P : Trivector N)
    (a b c : ConeCoordinateRing F) :
    coneBracket F P a (b + c) = coneBracket F P a b + coneBracket F P a c := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_add (Ideal.Quotient.mk (Ideal.span {F})) y z,
    coneBracket_mk, coneBracket_mk, coneBracket_mk]
  have he := congrArg (Ideal.Quotient.mk (Ideal.span {F}))
    (bracket_add_right (contractionCoefficients F P) x y z)
  simpa only [map_add, coneBracket_mk] using he

theorem coneBracket_leibniz_right (F : CubicPolynomial N) (P : Trivector N)
    (a b c : ConeCoordinateRing F) :
    coneBracket F P a (b * c) = coneBracket F P a b * c + b * coneBracket F P a c := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul (Ideal.Quotient.mk (Ideal.span {F})) y z,
    coneBracket_mk, coneBracket_mk, coneBracket_mk]
  have he := congrArg (Ideal.Quotient.mk (Ideal.span {F}))
    (bracket_leibniz_right (contractionCoefficients F P) x y z)
  simpa only [map_add, map_mul, coneBracket_mk] using he

/-- Polynomial Jacobi descends to all functions in the genuine cone coordinate ring. -/
theorem coneBracket_jacobi (F : CubicPolynomial N) (P : Trivector N)
    (hJ : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)))
    (a b c : ConeCoordinateRing F) :
    coneBracket F P a (coneBracket F P b c) + coneBracket F P b (coneBracket F P c a) +
      coneBracket F P c (coneBracket F P a b) = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective c
  have he := congrArg (Ideal.Quotient.mk (Ideal.span {F})) (hJ x y z)
  simpa only [map_add, map_zero, coneBracket_mk] using he

end NcCubic.Geometry
