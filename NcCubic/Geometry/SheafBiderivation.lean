module
public import NcCubic.Geometry.SheafKahler
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
universe u
/-- An alternating structure-sheaf biderivation, with no Jacobi requirement. -/
structure StructureSheafBiderivation (X : Scheme.{u}) extends StructureSheafBracket X where
  add_right (U) (a b c : Γ(X,U)) : bracket U a (b+c)=bracket U a b+bracket U a c
  skew (U) (a b : Γ(X,U)) : bracket U a b = -bracket U b a
  self_eq_zero (U) (a : Γ(X,U)) : bracket U a a=0
  leibniz (U) (a b c : Γ(X,U)) : bracket U a (b*c)=b*bracket U a c+c*bracket U a b

namespace StructureSheafBiderivation
variable {X : Scheme.{u}} (B : StructureSheafBiderivation X)
theorem add_left (U) (a b c : Γ(X,U)) :
    B.bracket U (a+b) c=B.bracket U a c+B.bracket U b c := by
  rw [B.skew,B.add_right,neg_add,← B.skew U a c,← B.skew U b c]
theorem leibniz_left (U) (a b c : Γ(X,U)) :
    B.bracket U (a*b) c=a*B.bracket U b c+b*B.bracket U a c := by
  rw [B.skew,B.leibniz,neg_add,← mul_neg,← mul_neg,← B.skew U b c,← B.skew U a c]
@[simp] theorem zero_right (U) (a : Γ(X,U)) : B.bracket U a 0=0 := by
  have h:=B.add_right U a 0 0
  simpa using h

def IsRelative {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ U a r,B.bracket U a (AffineSmoothness.coefficientMap f U r)=0

def hamiltonian {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (hR : B.IsRelative f) (U : X.Opens) (a : Γ(X,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Derivation R Γ(X,U) Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  refine Derivation.mk' {
    toFun := B.bracket U a
    map_add' := B.add_right U a
    map_smul' := ?_ } (B.leibniz U a)
  intro r b
  change B.bracket U a (AffineSmoothness.coefficientMap f U r*b)=
    AffineSmoothness.coefficientMap f U r*B.bracket U a b
  rw [B.leibniz,hR,mul_zero,add_zero]

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
    change B.bracket U (r • a) b=r • B.bracket U a b
    rw [B.skew]
    change -(B.hamiltonian f hR U b (r • a))=r • B.bracket U a b
    rw [Derivation.map_smul]
    change -(r • B.bracket U b a)=r • B.bracket U a b
    rw [← smul_neg,← B.skew U a b]
end StructureSheafBiderivation

def StructureSheafPoisson.toBiderivation {X : Scheme.{u}} (B : StructureSheafPoisson X) :
    StructureSheafBiderivation X where
  toStructureSheafBracket := B.toStructureSheafBracket
  add_right := B.add_right
  skew := B.skew
  self_eq_zero := B.self_eq_zero
  leibniz := B.leibniz
end NcCubic.Geometry
