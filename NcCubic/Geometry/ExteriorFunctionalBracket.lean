module
public import NcCubic.Geometry.ExteriorFunctionalContraction
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {X S : Scheme.{u}} (f : X ⟶ S)
set_option maxHeartbeats 1000000 in
theorem contractionGlobalBracket_differential_eval (c : Γ(tangentContractionSheaf f,⊤))
    (U : X.Opens) (a b : Γ(X,U)) :
    (contractionGlobalBracket f c).bracket U a b =
      tangentEvaluation f U (contractionEvaluation f U
        ((tangentContractionSheaf f).val.map (homOfLE le_top).op c)
          ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a))
        ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b) :=
  tangentSectionDerivation_apply f U _ b

variable (lam : Γ(dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)),⊤))
theorem exteriorFunctionalPairing_wedge (U : X.Opens)
    (a b : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    exteriorFunctionalPairing f lam U a b =
      dualPairing (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)) lam
        (Over.mk (homOfLE (show U≤⊤ from le_top))) (cotangentWedgeSection f U ![a,b]) := rfl

theorem exteriorFunctionalContraction_bracket (U : X.Opens) (a b : Γ(X,U)) :
    (contractionGlobalBracket f (exteriorFunctionalContraction f lam)).bracket U a b =
      dualPairing (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)) lam
        (Over.mk (homOfLE (show U≤⊤ from le_top)))
        (cotangentWedgeSection f U
          ![(Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a,(Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b]) :=
  (contractionGlobalBracket_differential_eval f (exteriorFunctionalContraction f lam) U a b).trans
    ((exteriorFunctionalContraction_eval f lam U
      ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a) ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b)).trans
      (exteriorFunctionalPairing_wedge f lam U _ _))

section Relative
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (B : StructureSheafBiderivation Y) (hR : B.IsRelative g)
/-- The actual cotangent exterior functional built from a biderivation contracts
back to the original operation on every actual open section ring. -/
theorem biderivationFunctionalContraction_bracket (U : Y.Opens) (a b : Γ(Y,U)) :
    (contractionGlobalBracket g (exteriorFunctionalContraction g
      (biderivationCotangentDualSection g B hR))).bracket U a b = B.bracket U a b :=
  (exteriorFunctionalContraction_bracket g (biderivationCotangentDualSection g B hR) U a b).trans
    (biderivationCotangentDualSection_d_wedge_d g B hR U a b)
end Relative
end NcCubic.Geometry
