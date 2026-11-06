/- Smooth scheme morphisms induce smooth coefficient maps on affine opens.
The base is transported from Γ(Spec R) to R using the canonical scheme isomorphism. -/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.AffineSmoothness
open AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
/-- The actual coefficient pullback R→Γ(Z,U) for a scheme over Spec R. -/
def coefficientMap (f : Z ⟶ Spec (CommRingCat.of R)) (U : Z.Opens) : R →+* Γ(Z,U) :=
  ((f.appLE ⊤ U le_top).hom).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- Scheme smoothness yields smoothness of this ring map on any affine source open. -/
theorem coefficientMap_smooth (f : Z ⟶ Spec (CommRingCat.of R))
    (U : Z.Opens) (hU : IsAffineOpen U) [Smooth f] :
    (coefficientMap f U).Smooth := by
  have hΓ := f.smooth_appLE (isAffineOpen_top _) hU le_top
  have he : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Smooth :=
    RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  exact he.comp hΓ

/-- The affine section ring is smooth as an R-algebra with its actual structure map. -/
theorem sections_smooth (f : Z ⟶ Spec (CommRingCat.of R))
    (U : Z.Opens) (hU : IsAffineOpen U) [Smooth f] :
    letI : Algebra R Γ(Z,U) := (coefficientMap f U).toAlgebra
    Algebra.Smooth R Γ(Z,U) :=
  (coefficientMap_smooth f U hU).toAlgebra
end NcCubic.Geometry.AffineSmoothness
