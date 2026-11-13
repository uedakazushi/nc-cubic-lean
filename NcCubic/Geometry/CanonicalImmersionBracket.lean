/- Canonical assembly from actual determinant evaluation: genuine immersion
bracket naturality and the actual bivector biderivation, without comparison hypotheses. -/
module
public import NcCubic.Geometry.CanonicalDeterminantFormula
public import NcCubic.Geometry.ImmersionBracketCompatibility
public import NcCubic.Geometry.DeterminantBiderivation
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
open ImmersionBivector
lemma bivectorSectionBracket_pullback {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (U : P.Opens) (piP : Γ(bivectorSheaf p,U)) (piX : Γ(bivectorSheaf (i ≫ p),i ⁻¹ᵁ U))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op U) piP) =
      (bivectorMap i p hΩ).val.app (op (i ⁻¹ᵁ U)) piX)
    (a b : Γ(P,U)) :
    (i.app U).hom (bivectorSectionBracket p U piP a b) =
      bivectorSectionBracket (i ≫ p) (i ⁻¹ᵁ U) piX ((i.app U).hom a) ((i.app U).hom b) :=
  bivectorSectionBracket_pullback_of_determinantFormulas i p hΩ
    (canonicalDeterminantPairing (Scheme.Hom.relativeDifferentials p))
    (canonicalDeterminantPairing ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)))
    (canonicalDeterminantPairing (Scheme.Hom.relativeDifferentials (i ≫ p)))
    (canonicalDeterminantPairing_hasDeterminantFormula _)
    (canonicalDeterminantPairing_hasDeterminantFormula _)
    (canonicalDeterminantPairing_hasDeterminantFormula _) U piP piX hext a b

lemma algebraicBivectorBracket_pullback {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op ⊤) piP) =
      (bivectorMap i p hΩ).val.app (op ⊤) piX)
    (U : P.Opens) (a b : Γ(P,U)) :
    (i.app U).hom ((algebraicBivectorBracket p piP).bracket U a b) =
      (algebraicBivectorBracket (i ≫ p) piX).bracket (i ⁻¹ᵁ U) ((i.app U).hom a) ((i.app U).hom b) :=
  algebraicBivectorBracket_pullback_of_determinantFormulas i p hΩ
    (canonicalDeterminantPairing (Scheme.Hom.relativeDifferentials p))
    (canonicalDeterminantPairing ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)))
    (canonicalDeterminantPairing (Scheme.Hom.relativeDifferentials (i ≫ p)))
    (canonicalDeterminantPairing_hasDeterminantFormula _)
    (canonicalDeterminantPairing_hasDeterminantFormula _)
    (canonicalDeterminantPairing_hasDeterminantFormula _) piP piX hext U a b
end NcCubic.Geometry.ImmersionBracketNaturality

namespace NcCubic.Geometry
open ImmersionBracketNaturality
/-- The actual bracket of an arbitrary genuine bivector, with all biderivation laws. -/
def algebraicBivectorBiderivation {X S : Scheme.{u}} (f : X ⟶ S) (pi : AlgebraicBivector f) :
    StructureSheafBiderivation X :=
  algebraicBivectorBiderivationOfDeterminant f
    (canonicalDeterminantPairing (Scheme.Hom.relativeDifferentials f))
    (canonicalDeterminantPairing_hasDeterminantFormula _) pi

@[simp] lemma algebraicBivectorBiderivation_toBracket {X S : Scheme.{u}} (f : X ⟶ S)
    (pi : AlgebraicBivector f) :
    (algebraicBivectorBiderivation f pi).toStructureSheafBracket = algebraicBivectorBracket f pi := rfl

lemma algebraicBivectorBiderivation_isRelative {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (pi : AlgebraicBivector f) :
    (algebraicBivectorBiderivation f pi).IsRelative f :=
  algebraicBivectorBiderivationOfDeterminant_isRelative f
    (canonicalDeterminantPairing (Scheme.Hom.relativeDifferentials f))
    (canonicalDeterminantPairing_hasDeterminantFormula _) pi
@[simp] lemma algebraicBivectorBracket_zero_left {X S : Scheme.{u}} (f : X ⟶ S)
    (pi : AlgebraicBivector f) (U : X.Opens) (a : Γ(X,U)) :
    (algebraicBivectorBracket f pi).bracket U 0 a = 0 := by
  change (algebraicBivectorBiderivation f pi).bracket U 0 a = 0
  rw [(algebraicBivectorBiderivation f pi).skew,
    (algebraicBivectorBiderivation f pi).zero_right,neg_zero]

@[simp] lemma algebraicBivectorBracket_zero_right {X S : Scheme.{u}} (f : X ⟶ S)
    (pi : AlgebraicBivector f) (U : X.Opens) (a : Γ(X,U)) :
    (algebraicBivectorBracket f pi).bracket U a 0 = 0 :=
  (algebraicBivectorBiderivation f pi).zero_right U a
end NcCubic.Geometry
