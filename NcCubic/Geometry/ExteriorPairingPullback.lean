/- Actual exterior determinant pairings commute with pullback and transposition.
The visible determinant evaluation laws are generic inputs until instantiated
with the canonical exterior-dual pairing. -/
module
public import NcCubic.Geometry.ExteriorHomExt
public import NcCubic.Geometry.TensorMapSections
public import NcCubic.Geometry.ExteriorPullbackSections
public import NcCubic.Geometry.ScalarPairingPullback
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
abbrev exteriorSquare (X : Scheme.{u}) (M : X.Modules) := Scheme.Modules.exteriorPower M (2:ℤ)
abbrev exteriorSquareTensor (X : Scheme.{u}) (M N : X.Modules) :=
  ((Tensor.sheafTensor X.sheaf).obj (exteriorSquare X M)).obj (exteriorSquare X N)
abbrev exteriorTensorWedges {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
    (v : Fin 2 → Γ(M,U)) (w : Fin 2 → Γ(N,U)) :=
  PullbackDual.tensorSheafPure X _ _ U
    (exteriorWedgeAlternating M U v ⊗ₜ[X.presheaf.obj (op U)] exteriorWedgeAlternating N U w)
/-- A visible evaluation law for an actual sheaf pairing; it is supplied by
canonical determinant constructions, not by a representation hypothesis. -/
def HasDeterminantFormula {X : Scheme.{u}} (M : X.Modules)
    (q : exteriorSquareTensor X (dualSheaf M) M ⟶ SheafOfModules.unit X.ringCatSheaf) : Prop :=
  ∀ (U : X.Opens) (v : Fin 2 → Γ(dualSheaf M,U)) (w : Fin 2 → Γ(M,U)),
    q.val.app (op U) (exteriorTensorWedges (dualSheaf M) M U v w) =
      dualPairing M (v 0) (Over.mk (𝟙 U)) (w 0) * dualPairing M (v 1) (Over.mk (𝟙 U)) (w 1) -
      dualPairing M (v 1) (Over.mk (𝟙 U)) (w 0) * dualPairing M (v 0) (Over.mk (𝟙 U)) (w 1)

lemma pullbackDualMap_unit_pairing {X P : Scheme.{u}} (i : X ⟶ P) (M : P.Modules)
    (U : P.Opens) (a : Γ(dualSheaf M,U)) (b : Γ(M,U)) :
    dualPairing ((Scheme.Modules.pullback i).obj M)
      ((PullbackDual.pullbackDualMap i M).val.app (op (i ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (dualSheaf M)).val.app (op U) a))
      (Over.mk (𝟙 (i ⁻¹ᵁ U)))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U) b) =
    (i.app U).hom (dualPairing M a (Over.mk (𝟙 U)) b) :=
  (PullbackDual.pullbackDualMap_eval i M (i ⁻¹ᵁ U) _ _).trans
    (PullbackDual.pullbackEvaluation_unit_tmul i M U a b)

def exteriorPullbackPairing {X P : Scheme.{u}} (i : X ⟶ P) (M : P.Modules)
    (q : exteriorSquareTensor X (dualSheaf ((Scheme.Modules.pullback i).obj M))
      ((Scheme.Modules.pullback i).obj M) ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ((Tensor.sheafTensor X.sheaf).obj ((Scheme.Modules.pullback i).obj (exteriorSquare P (dualSheaf M)))).obj
      ((Scheme.Modules.pullback i).obj (exteriorSquare P M)) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  tensorMap X.toRingedSpace
    ((ImmersionBivector.exteriorPullbackIso i (dualSheaf M) (2:ℤ)).hom ≫
      Scheme.Modules.exteriorPowerMap (PullbackDual.pullbackDualMap i M) (2:ℤ))
    (ImmersionBivector.exteriorPullbackIso i M (2:ℤ)).hom ≫ q
lemma pullbackScalarPairing_eq_exteriorPullbackPairing {X P : Scheme.{u}}
    (i : X ⟶ P) (M : P.Modules)
    (qP : exteriorSquareTensor P (dualSheaf M) M ⟶ SheafOfModules.unit P.ringCatSheaf)
    (qX : exteriorSquareTensor X (dualSheaf ((Scheme.Modules.pullback i).obj M))
      ((Scheme.Modules.pullback i).obj M) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hP : HasDeterminantFormula M qP)
    (hX : HasDeterminantFormula ((Scheme.Modules.pullback i).obj M) qX) :
    pullbackScalarPairing i (exteriorSquare P (dualSheaf M)) (exteriorSquare P M) qP =
      exteriorPullbackPairing i M qX := by
  apply pullback_tensor_exterior_pairing_ext i (dualSheaf M) M (SheafOfModules.unit X.ringCatSheaf)
  intro U v w
  let W := i ⁻¹ᵁ U
  let T := (Scheme.Modules.pullback i).obj M
  let va : Fin 2 → Γ(dualSheaf T,W) := fun j =>
    (PullbackDual.pullbackDualMap i M).val.app (op W)
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (dualSheaf M)).val.app (op U) (v j))
  let wb : Fin 2 → Γ(T,W) := fun j =>
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U) (w j))
  let s := (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (exteriorSquare P (dualSheaf M))).val.app (op U) (exteriorWedgeAlternating (dualSheaf M) U v))
  let t := (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (exteriorSquare P M)).val.app (op U) (exteriorWedgeAlternating M U w))
  let f := (ImmersionBivector.exteriorPullbackIso i (dualSheaf M) (2:ℤ)).hom ≫
    Scheme.Modules.exteriorPowerMap (PullbackDual.pullbackDualMap i M) (2:ℤ)
  let g := (ImmersionBivector.exteriorPullbackIso i M (2:ℤ)).hom
  have hf : f.val.app (op W) s = exteriorWedgeAlternating (dualSheaf T) W va :=
    (congrArg ((Scheme.Modules.exteriorPowerMap (PullbackDual.pullbackDualMap i M) (2:ℤ)).val.app (op W))
      (exteriorPullbackIso_unit_wedge i (dualSheaf M) U v)).trans
      (exteriorWedgeAlternating_map (PullbackDual.pullbackDualMap i M) W _)
  have hg : g.val.app (op W) t = exteriorWedgeAlternating T W wb :=
    exteriorPullbackIso_unit_wedge i M U w
  have ht := tensorMap_tmul X.toRingedSpace f g W s t
  have hr := (congrArg (qX.val.app (op W)) ht).trans
    ((congrArg₂ (fun a b => qX.val.app (op W)
      (PullbackDual.tensorSheafPure X _ _ W (a ⊗ₜ[X.presheaf.obj (op W)] b))) hf hg).trans
      (hX W va wb))
  have hl := (pullbackScalarPairing_unit_tmul i _ _ qP U
    (exteriorWedgeAlternating (dualSheaf M) U v) (exteriorWedgeAlternating M U w)).trans
      (congrArg (i.app U).hom (hP U v w))
  have hp (j k : Fin 2) :
      dualPairing T (va j) (Over.mk (𝟙 W)) (wb k) =
        (i.app U).hom (dualPairing M (v j) (Over.mk (𝟙 U)) (w k)) :=
    pullbackDualMap_unit_pairing i M U (v j) (w k)
  have hd :
      dualPairing T (va 0) (Over.mk (𝟙 W)) (wb 0) * dualPairing T (va 1) (Over.mk (𝟙 W)) (wb 1) -
        dualPairing T (va 1) (Over.mk (𝟙 W)) (wb 0) * dualPairing T (va 0) (Over.mk (𝟙 W)) (wb 1) =
      (i.app U).hom (dualPairing M (v 0) (Over.mk (𝟙 U)) (w 0) * dualPairing M (v 1) (Over.mk (𝟙 U)) (w 1) -
        dualPairing M (v 1) (Over.mk (𝟙 U)) (w 0) * dualPairing M (v 0) (Over.mk (𝟙 U)) (w 1)) := by
    rw [hp 0 0,hp 1 1,hp 1 0,hp 0 1]
    simp only [map_sub,map_mul]
  exact hl.trans (hd.symm.trans hr.symm)
lemma determinantPairing_natural {X : Scheme.{u}} (M N : X.Modules) (c : M ⟶ N)
    (qM : exteriorSquareTensor X (dualSheaf M) M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (qN : exteriorSquareTensor X (dualSheaf N) N ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hM : HasDeterminantFormula M qM) (hN : HasDeterminantFormula N qN) :
    tensorMap X.toRingedSpace (Scheme.Modules.exteriorPowerMap (dualMap c) (2:ℤ))
      (𝟙 (exteriorSquare X M)) ≫ qM =
    tensorMap X.toRingedSpace (𝟙 (exteriorSquare X (dualSheaf N)))
      (Scheme.Modules.exteriorPowerMap c (2:ℤ)) ≫ qN := by
  apply tensor_exterior_pairing_ext (dualSheaf N) M (SheafOfModules.unit X.ringCatSheaf)
  intro U v w
  let va := fun j => (dualMap c).val.app (op U) (v j)
  let wb := fun j => c.val.app (op U) (w j)
  have hv := exteriorWedgeAlternating_map (dualMap c) U v
  have hw := exteriorWedgeAlternating_map c U w
  have hl0 := tensorMap_tmul X.toRingedSpace (Scheme.Modules.exteriorPowerMap (dualMap c) (2:ℤ))
    (𝟙 (exteriorSquare X M)) U (exteriorWedgeAlternating (dualSheaf N) U v)
      (exteriorWedgeAlternating M U w)
  have hr0 := tensorMap_tmul X.toRingedSpace (𝟙 (exteriorSquare X (dualSheaf N)))
    (Scheme.Modules.exteriorPowerMap c (2:ℤ)) U (exteriorWedgeAlternating (dualSheaf N) U v)
      (exteriorWedgeAlternating M U w)
  have hl := (congrArg (qM.val.app (op U)) hl0).trans
    ((congrArg (fun a => qM.val.app (op U) (PullbackDual.tensorSheafPure X _ _ U
      (a ⊗ₜ[X.presheaf.obj (op U)] exteriorWedgeAlternating M U w))) hv).trans (hM U va w))
  have hr := (congrArg (qN.val.app (op U)) hr0).trans
    ((congrArg (fun b => qN.val.app (op U) (PullbackDual.tensorSheafPure X _ _ U
      (exteriorWedgeAlternating (dualSheaf N) U v ⊗ₜ[X.presheaf.obj (op U)] b))) hw).trans (hN U v wb))
  have hp (j k : Fin 2) : dualPairing M (va j) (Over.mk (𝟙 U)) (w k) =
      dualPairing N (v j) (Over.mk (𝟙 U)) (wb k) :=
    dualPairing_dualMap c (v j) (Over.mk (𝟙 U)) (w k)
  have hd :
      dualPairing M (va 0) (Over.mk (𝟙 U)) (w 0) * dualPairing M (va 1) (Over.mk (𝟙 U)) (w 1) -
        dualPairing M (va 1) (Over.mk (𝟙 U)) (w 0) * dualPairing M (va 0) (Over.mk (𝟙 U)) (w 1) =
      dualPairing N (v 0) (Over.mk (𝟙 U)) (wb 0) * dualPairing N (v 1) (Over.mk (𝟙 U)) (wb 1) -
        dualPairing N (v 1) (Over.mk (𝟙 U)) (wb 0) * dualPairing N (v 0) (Over.mk (𝟙 U)) (wb 1) := by
    rw [hp 0 0,hp 1 1,hp 1 0,hp 0 1]
  exact hl.trans (hd.trans hr.symm)
end NcCubic.Geometry.ImmersionBracketNaturality
