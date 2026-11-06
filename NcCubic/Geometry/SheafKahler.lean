/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.PoissonSheaf
public import NcCubic.Geometry.KahlerBracket
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.StructureSheafPoisson
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (B : StructureSheafPoisson X)

theorem leibniz_left (U : X.Opens) (a b c : Γ(X,U)) :
    B.bracket U (a*b) c = a*B.bracket U b c + b*B.bracket U a c := by
  rw [B.skew, B.leibniz, neg_add, ← mul_neg, ← mul_neg,
    ← B.skew U b c, ← B.skew U a c]

/-- The actual relative sheaf bracket is bilinear on each actual section ring. -/
def linearBracket {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (hR : B.IsRelative f) (U : X.Opens) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Γ(X,U) →ₗ[R] Γ(X,U) →ₗ[R] Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  refine { toFun := fun a => (B.hamiltonian f hR U a).toLinearMap
           map_add' := ?_
           map_smul' := ?_ }
  · intro a b
    ext c
    exact B.add_left U a b c
  · intro r a
    ext b
    change B.bracket U (r • a) b = r • B.bracket U a b
    rw [B.skew]
    change -(B.hamiltonian f hR U b (r • a)) = _
    rw [Derivation.map_smul]
    change -(r • B.bracket U b a) = r • B.bracket U a b
    rw [← smul_neg, ← B.skew U a b]

/-- Canonical exterior cotangent evaluation for the genuine structure-sheaf
bracket on an open. This requires no local-freeness assumption. -/
def kahlerForm {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (hR : B.IsRelative f) (U : X.Opens) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    ⋀[Γ(X,U)]^2 (KaehlerDifferential R Γ(X,U)) →ₗ[Γ(X,U)] Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact kahlerExteriorBracket (B.linearBracket f hR U) (B.leibniz U)
    (B.leibniz_left U) (B.skew U) (B.self_eq_zero U)

@[simp] theorem kahlerForm_d_wedge_d {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (hR : B.IsRelative f) (U : X.Opens)
    (a b : Γ(X,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    B.kahlerForm f hR U
      (exteriorPower.ιMulti Γ(X,U) 2 ![KaehlerDifferential.D R Γ(X,U) a,
        KaehlerDifferential.D R Γ(X,U) b]) = B.bracket U a b := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact kahlerExteriorBracket_d_wedge_d _ _ _ _ _ a b
end NcCubic.Geometry.StructureSheafPoisson
