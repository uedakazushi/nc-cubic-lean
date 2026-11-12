module
public import NcCubic.Geometry.DualFunctionalPullback
public import NcCubic.Geometry.ImmersionBracketNaturality
public import NcCubic.Geometry.ExteriorFunctionalBracket
public import NcCubic.Geometry.ContractionFaithfulness
public import NcCubic.Geometry.OpenPullbackSections
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Y : Scheme.{u}}
theorem dualMorphism_global_pairing {M N : Y.Modules} (Φ : M ⟶ dualSheaf N)
    (p : Γ(M,⊤)) (U : Y.Opens) (s : Γ(N,U)) :
    dualPairing N (Φ.app ⊤ p) (Over.mk (homOfLE (show U≤⊤ from le_top))) s =
      evalAt N (Φ.app U (M.presheaf.map (homOfLE le_top).op p)) s := by
  have hn : Φ.app U (M.presheaf.map (homOfLE le_top).op p) =
      (dualSheaf N).presheaf.map (homOfLE le_top).op (Φ.app ⊤ p) :=
    PresheafOfModules.naturality_apply Φ.val (homOfLE (show U≤⊤ from le_top)).op p
  have hp := dualPairing_map N (show U≤⊤ from le_top) (Φ.app ⊤ p) (Over.mk (𝟙 U)) s
  have hr : evalAt N ((dualSheaf N).presheaf.map (homOfLE le_top).op (Φ.app ⊤ p)) s =
      dualPairing N (Φ.app ⊤ p) (Over.mk (homOfLE (show U≤⊤ from le_top))) s := by
    exact hp
  exact hr.symm.trans (congrArg (fun q => evalAt N q s) hn).symm

variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem tangentWedgeSection_native (U : X.Opens) (v : Fin 2 → Γ(tangentSheaf f,U)) :
    exteriorWedgeAlternating (tangentSheaf f) U v = tangentWedgeSection f U
      (fun i => (siteSectionSemilinearEquiv (tangentSheaf f) U).symm (v i)) :=
  exteriorWedgeAlternating_eval (tangentSheaf f) U v

theorem bivectorSectionBracket_nativeWedge (U : X.Opens)
    (v : Fin 2 → Γ(tangentSheaf f,U)) (a b : Γ(X,U)) :
    bivectorSectionBracket f U (exteriorWedgeAlternating (tangentSheaf f) U v) a b =
      tangentEvaluation f U (v 0) ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a) *
        tangentEvaluation f U (v 1) ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b) -
      tangentEvaluation f U (v 1) ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a) *
        tangentEvaluation f U (v 0) ((Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b) := by
  rw [tangentWedgeSection_native]
  have h := bivectorSectionBracket_wedge f U
    (fun i => (siteSectionSemilinearEquiv (tangentSheaf f) U).symm (v i)) a b
  simpa only [LinearEquiv.apply_symm_apply,tangentSectionDerivation_apply] using h

/-- The scalar determinant characterization only on genuine local exterior generators. -/
def HasUnitDeterminantFormula
    (Φ : bivectorSheaf f ⟶ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))) : Prop :=
  ∀ (U : X.Opens) (v : Fin 2 → Γ(tangentSheaf f,U))
    (a b : Γ(Scheme.Hom.relativeDifferentials f,U)),
    evalAt (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))
      (Φ.app U (exteriorWedgeAlternating (tangentSheaf f) U v))
      (cotangentWedgeSection f U ![a,b]) =
    tangentEvaluation f U (v 0) a * tangentEvaluation f U (v 1) b -
      tangentEvaluation f U (v 1) a * tangentEvaluation f U (v 0) b

theorem dualFunctionalPullback_eq_bivectorFunctionPairing
    (Φ : bivectorSheaf f ⟶ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)))
    (hΦ : HasUnitDeterminantFormula f Φ) (U : X.Opens) (a b : Γ(X,U)) :
    dualFunctionalPullback Φ U (cotangentWedgeSection f U
      ![(Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a,
        (Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b]) =
      ImmersionBracketNaturality.bivectorFunctionPairing f U a b := by
  apply ImmersionBracketNaturality.exteriorDual_ext_on_wedges (tangentSheaf f) U
  intro Z v
  have hleft := dualFunctionalPullback_pair Φ U (cotangentWedgeSection f U
    ![(Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a,
      (Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b]) Z
    (exteriorWedgeAlternating (tangentSheaf f) Z.left v)
  have hrest := cotangentDifferentialWedge_natural f Z.hom a b
  have hdet := hΦ Z.left v
    ((Scheme.Hom.universalRelativeDerivation f).d (X:=op Z.left) (X.presheaf.map Z.hom.op a))
    ((Scheme.Hom.universalRelativeDerivation f).d (X:=op Z.left) (X.presheaf.map Z.hom.op b))
  have hright := ImmersionBracketNaturality.bivectorFunctionPairing_eval_subopen f U a b Z
    (exteriorWedgeAlternating (tangentSheaf f) Z.left v)
  exact hleft.trans ((congrArg
    (evalAt (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))
      (Φ.app Z.left (exteriorWedgeAlternating (tangentSheaf f) Z.left v))) hrest).trans
    (hdet.trans ((bivectorSectionBracket_nativeWedge f Z.left v
      (X.presheaf.map Z.hom.op a) (X.presheaf.map Z.hom.op b)).symm.trans hright.symm)))

theorem unitDeterminant_eval_arbitrary
    (Φ : bivectorSheaf f ⟶ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)))
    (hΦ : HasUnitDeterminantFormula f Φ) (U : X.Opens) (π : Γ(bivectorSheaf f,U)) (a b : Γ(X,U)) :
    evalAt (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)) (Φ.app U π)
      (cotangentWedgeSection f U ![(Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a,
        (Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b]) =
      bivectorSectionBracket f U π a b := by
  exact (dualFunctionalPullback_eval Φ U _ π).symm.trans
    ((congrArg (fun lam => evalAt (bivectorSheaf f) lam π)
      (dualFunctionalPullback_eq_bivectorFunctionPairing f Φ hΦ U a b)).trans
      (ImmersionBracketNaturality.bivectorFunctionPairing_eval f U a b π))

/-- A canonical unit-determinant map agrees on every actual open with the
existing exterior tangent contraction bracket, without global decomposability. -/
theorem exteriorFunctionalContraction_agrees_bracket
    (Φ : bivectorSheaf f ⟶ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)))
    (hΦ : HasUnitDeterminantFormula f Φ) (π : AlgebraicBivector f)
    (U : X.Opens) (a b : Γ(X,U)) :
    (contractionGlobalBracket f (exteriorFunctionalContraction f (Φ.app ⊤ π))).bracket U a b =
      (algebraicBivectorBracket f π).bracket U a b := by
  exact (exteriorFunctionalContraction_bracket f (Φ.app ⊤ π) U a b).trans
    ((dualMorphism_global_pairing Φ π U _).trans
      ((unitDeterminant_eval_arbitrary f Φ hΦ U
        ((bivectorSheaf f).presheaf.map (homOfLE le_top).op π) a b).trans
        (algebraicBivectorBracket_eq_sectionBracket f π U a b).symm))

section Relative
variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of R))
/-- Actual contraction agreement for every unit-determinant realization of
exterior tangent duality, over the genuine coefficient map. -/
theorem exteriorFunctionalContraction_agrees
    (Φ : bivectorSheaf g ⟶ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) (2:ℤ)))
    (hΦ : HasUnitDeterminantFormula g Φ) (π : AlgebraicBivector g) :
    exteriorFunctionalContraction g (Φ.app ⊤ π) = (bivectorContraction g).val.app (op ⊤) π := by
  apply contractionGlobalBracket_ext g
  intro U a b
  exact exteriorFunctionalContraction_agrees_bracket g Φ hΦ π U a b
/-- Recover a genuine bivector from a relative biderivation through an actual
exterior tangent-cotangent duality isomorphism. -/
def biderivationBivectorOfDuality
    (e : bivectorSheaf g ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) (2:ℤ)))
    (B : StructureSheafBiderivation Z) (hR : B.IsRelative g) : AlgebraicBivector g :=
  (CotangentCoordinates.moduleSectionsLinearEquiv e ⊤).symm
    (biderivationCotangentDualSection g B hR)

/-- The inverse construction recovers the original operation on every open;
only the determinant characterization of the given genuine duality is used. -/
theorem biderivationBivectorOfDuality_bracket
    (e : bivectorSheaf g ≅ dualSheaf
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) (2:ℤ)))
    (he : HasUnitDeterminantFormula g e.hom)
    (B : StructureSheafBiderivation Z) (hR : B.IsRelative g)
    (U : Z.Opens) (a b : Γ(Z,U)) :
    (algebraicBivectorBracket g (biderivationBivectorOfDuality g e B hR)).bracket U a b =
      B.bracket U a b := by
  have hl : e.hom.app ⊤ (biderivationBivectorOfDuality g e B hR) =
      biderivationCotangentDualSection g B hR :=
    (CotangentCoordinates.moduleSectionsLinearEquiv e ⊤).apply_symm_apply _
  exact (exteriorFunctionalContraction_agrees_bracket g e.hom he
    (biderivationBivectorOfDuality g e B hR) U a b).symm.trans
    ((congrArg (fun lam => (contractionGlobalBracket g
      (exteriorFunctionalContraction g lam)).bracket U a b) hl).trans
      (biderivationFunctionalContraction_bracket g B hR U a b))

end Relative
end NcCubic.Geometry
