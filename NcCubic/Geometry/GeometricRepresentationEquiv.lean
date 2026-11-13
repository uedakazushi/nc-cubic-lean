/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.HypersurfaceBivectorLinear
public import NcCubic.Geometry.GeometricRepresentation
public import NcCubic.ExteriorComparison
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ} {Z : Scheme}
variable (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
  [Smooth (ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
  (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
  (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
    (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
local notation "g" => ι ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n

/-- The actual canonical constant-trivector realization is a complex-linear
isomorphism, using genuine representation and uniqueness rather than dimensions. -/
def hypersurfaceBivectorEquiv :
    Trivector (n+1) ≃ₗ[ℂ] bivectorCoefficientSections g :=
  LinearEquiv.ofBijective (hypersurfaceBivectorLinear ι F hF hideal)
    ⟨hypersurfaceBivectorLinear_injective ι F hF hideal hN hF0,
      (hypersurfaceBivectorLinear_surjective_iff ι F hF hideal).2
        (fun pi => exists_standardRepresentative (by omega) ι F hF0 hF hideal pi)⟩

/-- The forward map is exactly the previously constructed actual bivector. -/
@[simp] theorem hypersurfaceBivectorEquiv_apply (P : Trivector (n+1)) :
    hypersurfaceBivectorEquiv ι hN F hF0 hF hideal P =
      hypersurfaceBivector ι F P hF hideal := rfl

/-- The inverse is the constant tensor representing the actual every-open
operation of the given genuine bivector section. -/
theorem hypersurfaceBivectorEquiv_symm_standardRepresentative
    (pi : bivectorCoefficientSections g) :
    HasStandardRepresentative ι F hF hideal pi
      ((hypersurfaceBivectorEquiv ι hN F hF0 hF hideal).symm pi) := by
  let e := hypersurfaceBivectorEquiv ι hN F hF0 hF hideal
  have he := e.apply_symm_apply pi
  intro U a b
  exact (congrArg (fun q : bivectorCoefficientSections g =>
      (algebraicBivectorBracket g q).bracket U a b) he.symm).trans
    (hypersurfaceBivector_standardRepresentative ι F (e.symm pi) hF hideal U a b)

/-- The original exterior cube maps to genuine global tangent bivectors,
with its actual complex coefficient action. -/
def hypersurfaceExteriorBivectorEquiv :
    (⋀[ℂ]^3 (CoordinateSpace (n+1))) ≃ₗ[ℂ] bivectorCoefficientSections g :=
  (exteriorTrivectorEquiv (n+1)).trans
    (hypersurfaceBivectorEquiv ι hN F hF0 hF hideal)

/-- Explicit gradient-contraction realization of the exterior-cube isomorphism. -/
@[simp] theorem hypersurfaceExteriorBivectorEquiv_apply
    (x : ⋀[ℂ]^3 (CoordinateSpace (n+1))) :
    hypersurfaceExteriorBivectorEquiv ι hN F hF0 hF hideal x =
      hypersurfaceBivector ι F (exteriorTrivectorEquiv (n+1) x) hF hideal := rfl

theorem hypersurfaceExteriorBivectorEquiv_standardRepresentative
    (x : ⋀[ℂ]^3 (CoordinateSpace (n+1))) :
    HasStandardRepresentative ι F hF hideal
      (hypersurfaceExteriorBivectorEquiv ι hN F hF0 hF hideal x)
      (exteriorTrivectorEquiv (n+1) x) :=
  hypersurfaceBivector_standardRepresentative ι F (exteriorTrivectorEquiv (n+1) x) hF hideal

/-- The induced operation is exactly the projectivized gradient contraction
on every actual open, spelling out the canonical forward-map formula. -/
theorem hypersurfaceExteriorBivectorEquiv_bracket
    (x : ⋀[ℂ]^3 (CoordinateSpace (n+1))) (U : Z.Opens) (a b : Γ(Z,U)) :
    (algebraicBivectorBracket g
      (hypersurfaceExteriorBivectorEquiv ι hN F hF0 hF hideal x)).bracket U a b =
      (hypersurfaceGlobalBracket ι F (exteriorTrivectorEquiv (n+1) x) hF hideal).bracket U a b :=
  hypersurfaceBivector_standardRepresentative ι F (exteriorTrivectorEquiv (n+1) x) hF hideal U a b
end NcCubic.Geometry
