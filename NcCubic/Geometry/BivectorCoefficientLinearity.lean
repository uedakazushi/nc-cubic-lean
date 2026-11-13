module
public import NcCubic.Geometry.BivectorLinearity
public import NcCubic.Geometry.AffineSmoothness
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Actual global bivectors as a coefficient-ring module, by restricting the
native global-function module along the genuine structure morphism. This is
an explicit module object, rather than an orphan scalar-action instance. -/
def bivectorCoefficientSections {R : Type u} [CommRing R] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of R)) : ModuleCat R :=
  (ModuleCat.restrictScalars (AffineSmoothness.coefficientMap g ⊤)).obj
    (ModuleCat.of Γ(X,⊤) (AlgebraicBivector g))

/-- Coefficient scalar multiplication of a genuine global bivector multiplies
its bracket by the actual coefficient section on every evaluation open. -/
theorem algebraicBivectorBracket_coefficient_smul
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of R)) (c : R) (pi : bivectorCoefficientSections g)
    (U : X.Opens) (a b : Γ(X,U)) :
    (algebraicBivectorBracket g (c • pi : bivectorCoefficientSections g)).bracket U a b =
      AffineSmoothness.coefficientMap g U c * (algebraicBivectorBracket g pi).bracket U a b := by
  have hc : X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (AffineSmoothness.coefficientMap g ⊤ c) = AffineSmoothness.coefficientMap g U c := by
    unfold AffineSmoothness.coefficientMap
    simp only [RingHom.comp_apply]
    exact congrArg (fun h => h ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
      (g.appLE_map (U := ⊤) (V := ⊤) (V' := U) le_top (homOfLE le_top).op)
  exact (algebraicBivectorBracket_smul g U (AffineSmoothness.coefficientMap g ⊤ c) pi a b).trans
    (congrArg (fun r => r * (algebraicBivectorBracket g pi).bracket U a b) hc)
end NcCubic.Geometry
