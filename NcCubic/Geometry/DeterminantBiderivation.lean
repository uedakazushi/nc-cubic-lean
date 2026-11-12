/- The actual bracket of a bivector is an alternating relative biderivation.
A visible determinant law supplies the alternating evaluation comparison. -/
module
public import NcCubic.Geometry.DeterminantBracketAgreement
public import NcCubic.Geometry.ContractionBracketLaws
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
lemma tensorPure_zero (Y : RingedSpace.{u,u})
    (F G : _root_.SheafOfModules.{u} (structureSheafRing Y))
    (U : TopologicalSpace.Opens Y.carrier) : toTensorSheafSection Y F G (op U) 0 = 0 :=
  ((sheafifyUnit Y (PresheafOfModules.tensorObj (O := Y.presheaf) F.val G.val)).app (op U)).hom.map_zero
variable {X S : Scheme.{u}} (f : X ⟶ S)
lemma bivectorSectionBracket_self_of_determinant
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials f) q)
    (U : X.Opens) (pi : Γ(bivectorSheaf f,U)) (a : Γ(X,U)) :
    bivectorSectionBracket f U pi a a = 0 := by
  have hw : exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials f) U
      ![(Scheme.Hom.universalRelativeDerivation f).d a,(Scheme.Hom.universalRelativeDerivation f).d a] = 0 :=
    (exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials f) U).map_eq_zero_of_eq _
      (i := (0:Fin 2)) (j := (1:Fin 2)) rfl (by decide)
  have h := determinantPairing_bracket f q hq U pi a a
  have hz : q.val.app (op U) (PullbackDual.tensorSheafPure X _ _ U
      (pi ⊗ₜ[X.presheaf.obj (op U)] (0 : Γ(exteriorSquare X (Scheme.Hom.relativeDifferentials f),U)))) = 0 :=
    (congrArg (fun t => q.val.app (op U) (PullbackDual.tensorSheafPure X _ _ U t))
      (TensorProduct.tmul_zero _ pi)).trans
      ((congrArg (q.val.app (op U)) (tensorPure_zero X.toRingedSpace _ _ U)).trans
        (q.val.app (op U)).hom.map_zero)
  exact h.symm.trans ((congrArg (fun z => q.val.app (op U)
    (PullbackDual.tensorSheafPure X _ _ U (pi ⊗ₜ[X.presheaf.obj (op U)] z))) hw).trans hz)

lemma algebraicBivectorBracket_self_of_determinant
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials f) q)
    (pi : AlgebraicBivector f) (U : X.Opens) (a : Γ(X,U)) :
    (algebraicBivectorBracket f pi).bracket U a a = 0 :=
  (algebraicBivectorBracket_eq_sectionBracket f pi U a a).trans
    (bivectorSectionBracket_self_of_determinant f q hq U _ a)

lemma algebraicBivectorBracket_skew_of_determinant
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials f) q)
    (pi : AlgebraicBivector f) (U : X.Opens) (a b : Γ(X,U)) :
    (algebraicBivectorBracket f pi).bracket U a b = -(algebraicBivectorBracket f pi).bracket U b a := by
  let c := (bivectorContraction f).val.app (op ⊤) pi
  have h := algebraicBivectorBracket_self_of_determinant f q hq pi U (a+b)
  have ha := algebraicBivectorBracket_self_of_determinant f q hq pi U a
  have hb := algebraicBivectorBracket_self_of_determinant f q hq pi U b
  change (contractionGlobalBracket f c).bracket U (a+b) (a+b) = 0 at h
  change (contractionGlobalBracket f c).bracket U a a = 0 at ha
  change (contractionGlobalBracket f c).bracket U b b = 0 at hb
  have hexp := (contractionGlobalBracket_add_left f c U a b (a+b)).trans
    (congrArg₂ (·+·) (contractionGlobalBracket_add_right f c U a a b)
      (contractionGlobalBracket_add_right f c U b a b))
  have hsum := hexp.symm.trans h
  have hs : (contractionGlobalBracket f c).bracket U a b +
      (contractionGlobalBracket f c).bracket U b a = 0 := by
    simpa only [ha,hb,zero_add,add_zero] using hsum
  exact eq_neg_of_add_eq_zero_left hs

def algebraicBivectorBiderivationOfDeterminant
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials f) q)
    (pi : AlgebraicBivector f) : StructureSheafBiderivation X where
  toStructureSheafBracket := algebraicBivectorBracket f pi
  add_right := contractionGlobalBracket_add_right f ((bivectorContraction f).val.app (op ⊤) pi)
  skew := algebraicBivectorBracket_skew_of_determinant f q hq pi
  self_eq_zero := algebraicBivectorBracket_self_of_determinant f q hq pi
  leibniz := contractionGlobalBracket_mul_right f ((bivectorContraction f).val.app (op ⊤) pi)

@[simp] lemma algebraicBivectorBiderivationOfDeterminant_toBracket
    (q : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials f))
      (Scheme.Hom.relativeDifferentials f) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials f) q) (pi : AlgebraicBivector f) :
    (algebraicBivectorBiderivationOfDeterminant f q hq pi).toStructureSheafBracket =
      algebraicBivectorBracket f pi := rfl

lemma algebraicBivectorBiderivationOfDeterminant_isRelative
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R))
    (q : exteriorSquareTensor Y (dualSheaf (Scheme.Hom.relativeDifferentials g))
      (Scheme.Hom.relativeDifferentials g) ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (hq : HasDeterminantFormula (Scheme.Hom.relativeDifferentials g) q) (pi : AlgebraicBivector g) :
    (algebraicBivectorBiderivationOfDeterminant g q hq pi).IsRelative g :=
  contractionGlobalBracket_coefficient_right g ((bivectorContraction g).val.app (op ⊤) pi)
end NcCubic.Geometry.ImmersionBracketNaturality
