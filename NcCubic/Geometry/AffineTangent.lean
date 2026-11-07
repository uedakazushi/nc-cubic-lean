/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local affine section comparisons; pinned upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.AffineLocalHom
public import NcCubic.Geometry.AffineCotangentSections
public import NcCubic.Geometry.TangentRelative
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
/-- Actual affine-open tangent sections are the dual of actual cotangent sections. -/
def affineTangentEvaluationEquiv (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Γ(tangentSheaf f,U) ≃ₗ[Γ(X,U)]
      Module.Dual Γ(X,U) Γ(Scheme.Hom.relativeDifferentials f,U) := by
  let : (Scheme.Hom.relativeDifferentials f).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials f
  exact LinearEquiv.ofBijective (tangentEvaluationLinear f U)
    (localHomFamily_eval_bijective (Scheme.Hom.relativeDifferentials f)
      (SheafOfModules.unit (structureSheaf X.sheaf)) U hU)
/-- The genuine tangent sheaf over an affine open is the dual of the ring's Kähler module. -/
def affineTangentKahlerDualEquiv (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Γ(tangentSheaf f,U) ≃ₗ[Γ(X,U)]
      Module.Dual Γ(X,U) (KaehlerDifferential R Γ(X,U)) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact (affineTangentEvaluationEquiv f U hU).trans
    (LinearEquiv.arrowCongr (affineCotangentSectionsEquiv f U hU)
      (LinearEquiv.refl Γ(X,U) Γ(X,U)))
/-- Actual relative tangent sections over an affine open are actual R-derivations. -/
def affineTangentDerivationEquiv (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Γ(tangentSheaf f,U) ≃ₗ[Γ(X,U)] Derivation R Γ(X,U) Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact (affineTangentKahlerDualEquiv f U hU).trans
    (KaehlerDifferential.linearMapEquivDerivation (M := Γ(X,U)) R Γ(X,U))

@[simp] theorem affineTangentKahlerDualEquiv_d (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (t : Γ(tangentSheaf f,U)) (a : Γ(X,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    affineTangentKahlerDualEquiv f U hU t (KaehlerDifferential.D R Γ(X,U) a) =
      tangentEvaluation f U t ((Scheme.Hom.universalRelativeDerivation f).d a) := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  change tangentEvaluation f U t ((affineCotangentSectionsEquiv f U hU).symm
    (KaehlerDifferential.D R Γ(X,U) a)) = _
  have hh := congrArg (affineCotangentSectionsEquiv f U hU).symm
    (affineCotangentSectionsEquiv_d f U hU a)
  exact congrArg (tangentEvaluation f U t)
    (hh.symm.trans ((affineCotangentSectionsEquiv f U hU).symm_apply_apply _))

/-- This equivalence is the canonical evaluation map already defined on all opens. -/
theorem affineTangentKahlerDualEquiv_eq (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (t : Γ(tangentSheaf f,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    affineTangentKahlerDualEquiv f U hU t = tangentSectionKahlerDual f U t := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  apply (KaehlerDifferential.linearMapEquivDerivation (M := Γ(X,U)) R Γ(X,U)).injective
  ext a
  change affineTangentKahlerDualEquiv f U hU t (KaehlerDifferential.D R Γ(X,U) a) =
    tangentSectionKahlerDual f U t (KaehlerDifferential.D R Γ(X,U) a)
  exact (affineTangentKahlerDualEquiv_d f U hU t a).trans
    (tangentSectionKahlerDual_d f U t a).symm

@[simp] theorem affineTangentDerivationEquiv_apply (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (t : Γ(tangentSheaf f,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    affineTangentDerivationEquiv f U hU t = tangentSectionRelativeDerivation f U t := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  ext a
  exact affineTangentKahlerDualEquiv_d f U hU t a

end NcCubic.Geometry
