/- Pulling back actual scalar pairings, with literal unit-section evaluation. -/
module
public import NcCubic.Geometry.TensorPullbackExt
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open RingedSpaceModuleAdjunction
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
variable {X P : Scheme.{u}}
def pullbackScalarPairing (i : X ⟶ P) (A B : P.Modules)
    (q : ((Tensor.sheafTensor P.sheaf).obj A).obj B ⟶ SheafOfModules.unit P.ringCatSheaf) :
    ((Tensor.sheafTensor X.sheaf).obj ((Scheme.Modules.pullback i).obj A)).obj
      ((Scheme.Modules.pullback i).obj B) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (PullbackDual.pullbackTensorIso i A B).inv ≫
    (modulePullback i.toLRSHom.toShHom).map q ≫
    SheafOfModules.pullbackObjUnitToUnit (structureSheafHom i.toLRSHom.toShHom)

lemma pullbackScalarPairing_unit_tmul (i : X ⟶ P) (A B : P.Modules)
    (q : ((Tensor.sheafTensor P.sheaf).obj A).obj B ⟶ SheafOfModules.unit P.ringCatSheaf)
    (U : P.Opens) (a : Γ(A,U)) (b : Γ(B,U)) :
    (pullbackScalarPairing i A B q).val.app (op (i ⁻¹ᵁ U))
      (PullbackDual.tensorSheafPure X ((Scheme.Modules.pullback i).obj A)
        ((Scheme.Modules.pullback i).obj B) (i ⁻¹ᵁ U)
        ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A).val.app (op U) a)
          ⊗ₜ[X.presheaf.obj (op (i ⁻¹ᵁ U))]
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B).val.app (op U) b))) =
    (i.app U).hom (q.val.app (op U)
      (PullbackDual.tensorSheafPure P A B U (a ⊗ₜ[P.presheaf.obj (op U)] b))) := by
  let z := PullbackDual.tensorSheafPure P A B U (a ⊗ₜ[P.presheaf.obj (op U)] b)
  let W := i ⁻¹ᵁ U
  let e := PullbackDual.pullbackTensorIso i A B
  let pbz := (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _).val.app (op U) z)
  have hc : e.hom ≫ pullbackScalarPairing i A B q =
      (modulePullback i.toLRSHom.toShHom).map q ≫
        SheafOfModules.pullbackObjUnitToUnit (structureSheafHom i.toLRSHom.toShHom) :=
    Iso.hom_inv_id_assoc e _
  have hca := congrArg (fun k => k.val.app (op W) pbz) hc
  have ht := PullbackDual.comparison_tensorSheafPure i A B U a b
  have hu := PullbackDual.pullback_map_unit_app i q U z
  have ho := PullbackDual.pullbackObjUnitToUnit_unit_app i U (q.val.app (op U) z)
  exact (congrArg ((pullbackScalarPairing i A B q).val.app (op W)) ht).symm.trans
    (hca.trans ((congrArg
      ((SheafOfModules.pullbackObjUnitToUnit (structureSheafHom i.toLRSHom.toShHom)).val.app (op W))
      hu).trans ho))
end NcCubic.Geometry.ImmersionBracketNaturality
