/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local affine section comparisons; pinned upstream dependencies retain their licenses. -/
module
public import StacksFrontier.AlgebraicGeometry.AffineDifferentials.SpecKaehlerEquiv
public import NcCubic.Geometry.AffineSmoothness
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
/-- The genuine affine-open differential comparison, with its actual base-section ring. -/
def affineCotangentSectionsIso (V : S.Opens) (U : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V) :
    (Scheme.Hom.relativeDifferentials f).val.obj (op U) ≅
      CommRingCat.KaehlerDifferential (f.appLE V U hUV) :=
  (Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
    f hU hUV hV).choose
@[simp] theorem affineCotangentSectionsIso_d (V : S.Opens) (U : X.Opens)
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    (a : Γ(X,U)) :
    (affineCotangentSectionsIso f V U hV hU hUV).hom.hom
      ((Scheme.Hom.universalRelativeDerivation f).d a) =
      CommRingCat.KaehlerDifferential.d a :=
  (Stacks.AlgebraicGeometry.AffineDifferentialsIso.existsUnique_affineDifferentialsIso
    f hU hUV hV).choose_spec.1 a

section AffineBase
variable {R : Type u} [CommRing R]
/-- Transport over the canonical isomorphism R≅Γ(Spec R,⊤), with the target
section ring fixed. -/
def coefficientKaehlerEquiv (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    KaehlerDifferential R Γ(X,U) ≃ₗ[Γ(X,U)]
      CommRingCat.KaehlerDifferential (f.appLE ⊤ U le_top) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  let coeff : CommRingCat.of R ⟶ Γ(X,U) :=
    CommRingCat.ofHom (AffineSmoothness.coefficientMap f U)
  have fac : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top =
      coeff ≫ 𝟙 (Γ(X,U)) := by rfl
  exact LinearEquiv.ofBijective (CommRingCat.KaehlerDifferential.map fac).hom
    (CommRingCat.KaehlerDifferential.bijective_map fac)

@[simp] theorem coefficientKaehlerEquiv_d (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (a : Γ(X,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    coefficientKaehlerEquiv f U (KaehlerDifferential.D R Γ(X,U) a) =
      CommRingCat.KaehlerDifferential.d a := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact CommRingCat.KaehlerDifferential.map_d
    (show (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U le_top =
      CommRingCat.ofHom (AffineSmoothness.coefficientMap f U) ≫ 𝟙 (Γ(X,U)) from rfl) a

/-- Affine-open relative cotangent sections agree with differentials over the
actual coefficient ring R, rather than over Γ(Spec R,⊤). -/
def affineCotangentSectionsEquiv (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Γ(Scheme.Hom.relativeDifferentials f,U) ≃ₗ[Γ(X,U)]
      KaehlerDifferential R Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  let e := affineCotangentSectionsIso f ⊤ U (isAffineOpen_top _) hU le_top
  let eΓ : Γ(Scheme.Hom.relativeDifferentials f,U) ≃ₗ[Γ(X,U)]
      CommRingCat.KaehlerDifferential (f.appLE ⊤ U le_top) := by
    exact e.toLinearEquiv
  exact eΓ.trans (coefficientKaehlerEquiv f U).symm

@[simp] theorem affineCotangentSectionsEquiv_d (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.Opens) (hU : IsAffineOpen U) (a : Γ(X,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    affineCotangentSectionsEquiv f U hU
      ((Scheme.Hom.universalRelativeDerivation f).d a) =
      KaehlerDifferential.D R Γ(X,U) a := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  change (coefficientKaehlerEquiv f U).symm
    ((affineCotangentSectionsIso f ⊤ U (isAffineOpen_top _) hU le_top).hom.hom
      ((Scheme.Hom.universalRelativeDerivation f).d a)) = _
  have hd := congrArg (coefficientKaehlerEquiv f U).symm (coefficientKaehlerEquiv_d f U a)
  exact (congrArg (coefficientKaehlerEquiv f U).symm
    (affineCotangentSectionsIso_d f ⊤ U (isAffineOpen_top _) hU le_top a)).trans
      (hd.symm.trans ((coefficientKaehlerEquiv f U).symm_apply_apply _))
end AffineBase

end NcCubic.Geometry
