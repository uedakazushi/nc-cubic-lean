/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
The base-isomorphism adapter is adapted from StacksFrontier.RingTheory.Kaehler.FormsTransport
at pinned Stacks revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache 2.0).
Focused Kähler-coordinate helpers avoid unrelated de Rham and different-divisor imports. -/
module
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
@[expose] public noncomputable section
namespace NcCubic.Geometry.CotangentCoordinates
universe u

/-- Changing the base ring by a compatible actual ring isomorphism preserves
Kähler differentials, as a linear equivalence over the unchanged algebra. -/
def kaehlerBaseEquiv {Λ R B : Type u} [CommRing Λ] [CommRing R] [CommRing B]
    [Algebra Λ B] [Algebra R B] (b : Λ ≃+* R)
    (h : ∀ l, algebraMap Λ B l = algebraMap R B (b l)) :
    Ω[B⁄Λ] ≃ₗ[B] Ω[B⁄R] := by
  letI : Algebra Λ R := b.toRingHom.toAlgebra
  haveI : IsScalarTower Λ R B := .of_algebraMap_eq h
  letI : Algebra R Λ := b.symm.toRingHom.toAlgebra
  haveI : IsScalarTower R Λ B := .of_algebraMap_eq fun r => by
    change algebraMap R B r = algebraMap Λ B (b.symm r)
    rw [h, RingEquiv.apply_symm_apply]
  exact LinearEquiv.ofLinearMap (KaehlerDifferential.map Λ R B B)
    (KaehlerDifferential.map R Λ B B)
    (Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun x => by simp))
    (Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun x => by simp))

/-- A genuine polynomial algebra chart gives a basis of its Kähler differentials.
The coordinate basis is transported through an étale (indeed isomorphic) change
of algebra, rather than supplied as a rank assumption. -/
def polynomialKahlerBasis {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type u} (e : MvPolynomial ι R ≃ₐ[R] B) :
    Module.Basis ι B Ω[B⁄R] := by
  letI : Algebra (MvPolynomial ι R) B := e.toRingHom.toAlgebra
  letI : IsScalarTower R (MvPolynomial ι R) B :=
    .of_algebraMap_eq fun r => (e.commutes r).symm
  let eA : MvPolynomial ι R ≃ₐ[MvPolynomial ι R] B :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale (MvPolynomial ι R) B :=
    Algebra.FormallyEtale.of_equiv eA
  exact ((KaehlerDifferential.mvPolynomialBasis R ι).baseChange B).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (MvPolynomial ι R) B)

end NcCubic.Geometry.CotangentCoordinates
