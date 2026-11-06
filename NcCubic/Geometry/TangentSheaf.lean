module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomLeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom

@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u

/-- The actual relative tangent sheaf, the sheaf dual of relative Kähler differentials. -/
def tangentSheaf {X S : Scheme.{u}} (f : X ⟶ S) : X.Modules :=
  { val := internalHom X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
      (SheafOfModules.unit (structureSheaf X.sheaf)).val
    isSheaf := internalHom_isSheaf X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
      (SheafOfModules.unit (structureSheaf X.sheaf)).val
      (SheafOfModules.unit (structureSheaf X.sheaf)).isSheaf }

/-- Evaluate an actual tangent-sheaf section on a local differential. -/
def tangentEvaluation {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (t : Γ(tangentSheaf f, U)) :
    Γ(Scheme.Hom.relativeDifferentials f, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (t.app (op (Over.mk (𝟙 U)))).hom

/-- An actual tangent-sheaf section acts as a derivation on the ring of local functions. -/
def tangentSectionDerivation {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (t : Γ(tangentSheaf f, U)) :
    Derivation ℤ Γ(X, U) Γ(X, U) :=
  Derivation.mk'
    (((tangentEvaluation f U t).toAddMonoidHom.comp
      (Scheme.Hom.universalRelativeDerivation f).d).toIntLinearMap)
    (by intro a b
        change tangentEvaluation f U t ((Scheme.Hom.universalRelativeDerivation f).d (a*b)) =
          a * tangentEvaluation f U t ((Scheme.Hom.universalRelativeDerivation f).d b) +
          b * tangentEvaluation f U t ((Scheme.Hom.universalRelativeDerivation f).d a)
        have hd := (Scheme.Hom.universalRelativeDerivation f).d_mul a b
        exact (congrArg (tangentEvaluation f U t) hd).trans
          (((tangentEvaluation f U t).map_add _ _).trans
            (congrArg₂ (· + ·) ((tangentEvaluation f U t).map_smul a _)
              ((tangentEvaluation f U t).map_smul b _))))

@[simp] theorem tangentSectionDerivation_apply {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (t : Γ(tangentSheaf f, U)) (a : Γ(X, U)) :
    tangentSectionDerivation f U t a =
      tangentEvaluation f U t ((Scheme.Hom.universalRelativeDerivation f).d a) := rfl

/-- Relative tangent sections kill functions pulled back from the base. -/
@[simp] theorem tangentSectionDerivation_base {X S : Scheme.{u}} (f : X ⟶ S)
    (W : S.Opens) (t : Γ(tangentSheaf f, f ⁻¹ᵁ W)) (a : Γ(S, W)) :
    tangentSectionDerivation f (f ⁻¹ᵁ W) t ((f.app W).hom a) = 0 := by
  exact (congrArg (tangentEvaluation f (f ⁻¹ᵁ W) t)
    (Scheme.Hom.universalRelativeDerivation_d_app_eq_zero f W a)).trans
      (map_zero _)

end NcCubic.Geometry
