module
public import NcCubic.Geometry.CanonicalImmersionBracket
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite ImmersionBivector
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The actual geometric extension relation for bivectors. This is exactly
the pullback-adjunction unit equality with the canonical immersion bivector
map, not a bracket comparison or a classification hypothesis. -/
def BivectorExtends {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p)) : Prop :=
  (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op ⊤) piP) =
    (bivectorMap i p hΩ).val.app (op ⊤) piX

/-- Unfolding the named geometric relation gives the literal unit equality. -/
theorem bivectorExtends_iff {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p)) :
    BivectorExtends i p hΩ piP piX ↔
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op ⊤) piP) =
        (bivectorMap i p hΩ).val.app (op ⊤) piX := Iff.rfl

/-- A genuine extension of intrinsic bivectors preserves the kernel of the
actual ambient-to-intrinsic section map. The statement is generic in the
schemes, so applications do not unfold a concrete projective presentation. -/
theorem algebraicBivectorBracket_pullback_zero_left
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op ⊤) piP) =
      (bivectorMap i p hΩ).val.app (op ⊤) piX)
    (U : P.Opens) (a b : Γ(P,U)) (ha : (i.app U).hom a = 0) :
    (i.app U).hom ((algebraicBivectorBracket p piP).bracket U a b) = 0 := by
  exact (ImmersionBracketNaturality.algebraicBivectorBracket_pullback
    i p hΩ piP piX hext U a b).trans
    ((congrArg (fun z : Γ(X,i ⁻¹ᵁ U) =>
      (algebraicBivectorBracket (i ≫ p) piX).bracket (i ⁻¹ᵁ U) z ((i.app U).hom b)) ha).trans
      (algebraicBivectorBracket_zero_left (i ≫ p) piX (i ⁻¹ᵁ U) ((i.app U).hom b)))
/-- An ambient operation explicitly compared with a genuine extended
bivector preserves the same section kernel. The comparison remains visible. -/
theorem structureSheafBracket_pullback_zero_left_of_extension
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op ⊤) piP) =
      (bivectorMap i p hΩ).val.app (op ⊤) piX)
    (B : StructureSheafBracket P)
    (heq : ∀ U a b, B.bracket U a b = (algebraicBivectorBracket p piP).bracket U a b)
    (U : P.Opens) (a b : Γ(P,U)) (ha : (i.app U).hom a = 0) :
    (i.app U).hom (B.bracket U a b) = 0 := by
  exact (congrArg (i.app U).hom (heq U a b)).trans
    (algebraicBivectorBracket_pullback_zero_left i p hΩ piP piX hext U a b ha)
/-- Genuine geometric extension implies equality of the actual operations
under pullback. No bracket-comparison premise is needed. -/
theorem algebraicBivectorBracket_pullback_of_extends
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : BivectorExtends i p hΩ piP piX)
    (U : P.Opens) (a b : Γ(P,U)) :
    (i.app U).hom ((algebraicBivectorBracket p piP).bracket U a b) =
      (algebraicBivectorBracket (i ≫ p) piX).bracket (i ⁻¹ᵁ U) ((i.app U).hom a) ((i.app U).hom b) :=
  ImmersionBracketNaturality.algebraicBivectorBracket_pullback i p hΩ piP piX hext U a b

theorem algebraicBivectorBracket_pullback_zero_left_of_extends
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : BivectorExtends i p hΩ piP piX)
    (U : P.Opens) (a b : Γ(P,U)) (ha : (i.app U).hom a = 0) :
    (i.app U).hom ((algebraicBivectorBracket p piP).bracket U a b) = 0 :=
  algebraicBivectorBracket_pullback_zero_left i p hΩ piP piX hext U a b ha

theorem structureSheafBracket_pullback_zero_left_of_extends
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : BivectorExtends i p hΩ piP piX)
    (B : StructureSheafBracket P)
    (heq : ∀ U a b, B.bracket U a b = (algebraicBivectorBracket p piP).bracket U a b)
    (U : P.Opens) (a b : Γ(P,U)) (ha : (i.app U).hom a = 0) :
    (i.app U).hom (B.bracket U a b) = 0 :=
  structureSheafBracket_pullback_zero_left_of_extension i p hΩ piP piX hext B heq U a b ha
/-- A specified ambient operation agrees on every actual open with the
intrinsic operation whenever its genuine bivector geometrically extends. -/
theorem bracket_pullback_of_extends_and_eq
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : BivectorExtends i p hΩ piP piX)
    (B : StructureSheafBracket P)
    (hB : ∀ U a b, B.bracket U a b = (algebraicBivectorBracket p piP).bracket U a b)
    (U : P.Opens) (a b : Γ(P,U)) :
    (i.app U).hom (B.bracket U a b) =
      (algebraicBivectorBracket (i ≫ p) piX).bracket (i ⁻¹ᵁ U) ((i.app U).hom a) ((i.app U).hom b) :=
  (congrArg (i.app U).hom (hB U a b)).trans
    (algebraicBivectorBracket_pullback_of_extends i p hΩ piP piX hext U a b)
end NcCubic.Geometry
