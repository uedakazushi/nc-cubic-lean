/- Actual exterior evaluation through a genuine pullback/transpose extension. -/
module
public import NcCubic.Geometry.ExteriorPairingPullback
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
lemma exteriorAlongPullback_comp_transpose {X P : Scheme.{u}} (i : X ⟶ P)
    (M : P.Modules) (N : X.Modules) (c : (Scheme.Modules.pullback i).obj M ⟶ N)
    (tau : dualSheaf N ⟶ (Scheme.Modules.pullback i).obj (dualSheaf M))
    (htau : tau ≫ PullbackDual.pullbackDualMap i M = dualMap c) :
    ImmersionBivector.exteriorAlongPullback i tau (2:ℤ) ≫
        (ImmersionBivector.exteriorPullbackIso i (dualSheaf M) (2:ℤ)).hom ≫
        Scheme.Modules.exteriorPowerMap (PullbackDual.pullbackDualMap i M) (2:ℤ) =
      Scheme.Modules.exteriorPowerMap (dualMap c) (2:ℤ) := by
  let d := Scheme.Modules.exteriorPowerMap (PullbackDual.pullbackDualMap i M) (2:ℤ)
  have h1 := congrArg (fun k => k ≫ d)
    (ImmersionBivector.exteriorAlongPullback_comp_comparison i tau (2:ℤ))
  exact (Category.assoc _ _ d).symm.trans (h1.trans
    ((Scheme.Modules.exteriorPowerMap_comp tau (PullbackDual.pullbackDualMap i M) (2:ℤ)).symm.trans
      (congrArg (fun k => Scheme.Modules.exteriorPowerMap k (2:ℤ)) htau)))

lemma determinant_evaluation_of_extension {X P : Scheme.{u}} (i : X ⟶ P)
    (M : P.Modules) (N : X.Modules) (c : (Scheme.Modules.pullback i).obj M ⟶ N)
    (tau : dualSheaf N ⟶ (Scheme.Modules.pullback i).obj (dualSheaf M))
    (htau : tau ≫ PullbackDual.pullbackDualMap i M = dualMap c)
    (qP : exteriorSquareTensor P (dualSheaf M) M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (qB : exteriorSquareTensor X (dualSheaf ((Scheme.Modules.pullback i).obj M))
      ((Scheme.Modules.pullback i).obj M) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (qX : exteriorSquareTensor X (dualSheaf N) N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hP : HasDeterminantFormula M qP)
    (hB : HasDeterminantFormula ((Scheme.Modules.pullback i).obj M) qB)
    (hX : HasDeterminantFormula N qX)
    (U : P.Opens) (piP : Γ(exteriorSquare P (dualSheaf M),U))
    (piX : Γ(exteriorSquare X (dualSheaf N),i ⁻¹ᵁ U))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (exteriorSquare P (dualSheaf M))).val.app (op U) piP) =
      (ImmersionBivector.exteriorAlongPullback i tau (2:ℤ)).val.app (op (i ⁻¹ᵁ U)) piX)
    (z : Γ(exteriorSquare P M,U)) :
    (i.app U).hom (qP.val.app (op U) (PullbackDual.tensorSheafPure P _ _ U
      (piP ⊗ₜ[P.presheaf.obj (op U)] z))) =
    qX.val.app (op (i ⁻¹ᵁ U)) (PullbackDual.tensorSheafPure X _ _ (i ⁻¹ᵁ U)
      (piX ⊗ₜ[X.presheaf.obj (op (i ⁻¹ᵁ U))]
        (Scheme.Modules.exteriorPowerMap c (2:ℤ)).val.app (op (i ⁻¹ᵁ U))
          ((ImmersionBivector.exteriorPullbackIso i M (2:ℤ)).hom.val.app (op (i ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
              (exteriorSquare P M)).val.app (op U) z)))) := by
  let W := i ⁻¹ᵁ U
  let T := (Scheme.Modules.pullback i).obj M
  let a := (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (exteriorSquare P (dualSheaf M))).val.app (op U) piP)
  let b := (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (exteriorSquare P M)).val.app (op U) z)
  let f := (ImmersionBivector.exteriorPullbackIso i (dualSheaf M) (2:ℤ)).hom ≫
    Scheme.Modules.exteriorPowerMap (PullbackDual.pullbackDualMap i M) (2:ℤ)
  let g := (ImmersionBivector.exteriorPullbackIso i M (2:ℤ)).hom
  let d := Scheme.Modules.exteriorPowerMap (dualMap c) (2:ℤ)
  have ha : f.val.app (op W) a = d.val.app (op W) piX :=
    (congrArg (f.val.app (op W)) hext).trans
      (congrArg (fun k => k.val.app (op W) piX)
        (exteriorAlongPullback_comp_transpose i M N c tau htau))
  have hp0 := pullbackScalarPairing_unit_tmul i _ _ qP U piP z
  have hp1 := congrArg (fun k => k.val.app (op W)
    (PullbackDual.tensorSheafPure X _ _ W (a ⊗ₜ[X.presheaf.obj (op W)] b)))
    (pullbackScalarPairing_eq_exteriorPullbackPairing i M qP qB hP hB)
  have hp2 := congrArg (qB.val.app (op W)) (tensorMap_tmul X.toRingedSpace f g W a b)
  have hp3 := congrArg (fun x => qB.val.app (op W)
    (PullbackDual.tensorSheafPure X _ _ W (x ⊗ₜ[X.presheaf.obj (op W)] g.val.app (op W) b))) ha
  have hn := congrArg (fun k => k.val.app (op W)
    (PullbackDual.tensorSheafPure X _ _ W (piX ⊗ₜ[X.presheaf.obj (op W)] g.val.app (op W) b)))
    (determinantPairing_natural T N c qB qX hB hX)
  have hnL := congrArg (qB.val.app (op W))
    (tensorMap_tmul X.toRingedSpace d (𝟙 (exteriorSquare X T)) W piX (g.val.app (op W) b))
  have hnR := congrArg (qX.val.app (op W))
    (tensorMap_tmul X.toRingedSpace (𝟙 (exteriorSquare X (dualSheaf N)))
      (Scheme.Modules.exteriorPowerMap c (2:ℤ)) W piX (g.val.app (op W) b))
  exact hp0.symm.trans (hp1.trans (hp2.trans (hp3.trans
    (hnL.symm.trans (hn.trans hnR)))))
end NcCubic.Geometry.ImmersionBracketNaturality
