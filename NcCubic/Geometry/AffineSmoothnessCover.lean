module
public import NcCubic.Geometry.AffineSmoothness
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.AffineSmoothness
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
/-- Smoothness can be checked on the actual coefficient maps of any affine open cover. -/
theorem smooth_of_coefficientMaps (f : Z ⟶ Spec (CommRingCat.of R)) {ι : Type*}
    (U : ι → Z.affineOpens) (hU : ⨆ i, (U i : Z.Opens) = ⊤)
    (hsmooth : ∀ i, (coefficientMap f (U i)).Smooth) : Smooth f := by
  apply HasRingHomProperty.of_iSup_eq_top (P := @Smooth) U hU
  intro i
  have he : ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom).Smooth :=
    RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.bijective
  convert he.comp (hsmooth i) using 1
  ext x
  simp [coefficientMap, RingHom.comp_apply]
end NcCubic.Geometry.AffineSmoothness
