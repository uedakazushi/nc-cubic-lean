module
public import NcCubic.Geometry.TangentSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
/-- The genuine exterior square of the relative tangent sheaf. -/
def bivectorSheaf {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules :=
  Scheme.Modules.exteriorPower (tangentSheaf f) (2 : ℤ)
/-- Actual global bivector sections of the exterior-square tangent sheaf. -/
abbrev AlgebraicBivector {X S : Scheme.{u}} (f : X ⟶ S) : Type u :=
  Γ(bivectorSheaf f, ⊤)
end NcCubic.Geometry
