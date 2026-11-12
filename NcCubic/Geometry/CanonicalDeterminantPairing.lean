/- Literal scalarization of the canonical exterior-dual pairing via tensor currying. -/
module
public import NcCubic.Geometry.ExteriorPairingPullback
public import NcCubic.Geometry.ExteriorRawPairing
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
variable {X : Scheme.{u}}
def scalarPairingOfMap (M : X.Modules)
    (Phi : exteriorSquare X (dualSheaf M) ⟶ dualSheaf (exteriorSquare X M)) :
    exteriorSquareTensor X (dualSheaf M) M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafTensorCurry.tensorHomEquiv X.toRingedSpace _ _ _).symm Phi

lemma scalarPairingOfMap_eval (M : X.Modules)
    (Phi : exteriorSquare X (dualSheaf M) ⟶ dualSheaf (exteriorSquare X M))
    (U : X.Opens) (s : Γ(exteriorSquare X (dualSheaf M),U)) (t : Γ(exteriorSquare X M,U)) :
    (scalarPairingOfMap M Phi).val.app (op U)
      (PullbackDual.tensorSheafPure X _ _ U (s ⊗ₜ[X.presheaf.obj (op U)] t)) =
    dualPairing (exteriorSquare X M) (Phi.val.app (op U) s) (Over.mk (𝟙 U)) t := by
  have hc := SheafTensorCurry.tensorHomEquiv_isTensorCurry X.toRingedSpace
    (scalarPairingOfMap M Phi) U s t
  have he : (SheafTensorCurry.tensorHomEquiv X.toRingedSpace
      (exteriorSquare X (dualSheaf M)) (exteriorSquare X M)
      (SheafOfModules.unit X.ringCatSheaf)) (scalarPairingOfMap M Phi) = Phi :=
    (SheafTensorCurry.tensorHomEquiv X.toRingedSpace
      (exteriorSquare X (dualSheaf M)) (exteriorSquare X M)
      (SheafOfModules.unit X.ringCatSheaf)).apply_symm_apply Phi
  exact hc.symm.trans (congrArg (fun k : exteriorSquare X (dualSheaf M) ⟶ dualSheaf (exteriorSquare X M) =>
    dualPairing (exteriorSquare X M)
    (k.val.app (op U) s) (Over.mk (𝟙 U)) t) he)

lemma scalarPairingOfMap_hasDeterminantFormula (M : X.Modules)
    (Phi : exteriorSquare X (dualSheaf M) ⟶ dualSheaf (exteriorSquare X M))
    (hPhi : ∀ (U : X.Opens) (v : Fin 2 → Γ(dualSheaf M,U)) (w : Fin 2 → Γ(M,U)),
      dualPairing (exteriorSquare X M) (Phi.val.app (op U) (exteriorWedgeAlternating (dualSheaf M) U v))
        (Over.mk (𝟙 U)) (exteriorWedgeAlternating M U w) =
      dualPairing M (v 0) (Over.mk (𝟙 U)) (w 0) * dualPairing M (v 1) (Over.mk (𝟙 U)) (w 1) -
        dualPairing M (v 1) (Over.mk (𝟙 U)) (w 0) * dualPairing M (v 0) (Over.mk (𝟙 U)) (w 1)) :
    HasDeterminantFormula M (scalarPairingOfMap M Phi) := by
  intro U v w
  exact (scalarPairingOfMap_eval M Phi U (exteriorWedgeAlternating (dualSheaf M) U v)
    (exteriorWedgeAlternating M U w)).trans (hPhi U v w)

def canonicalDeterminantPairing (M : X.Modules) :
    exteriorSquareTensor X (dualSheaf M) M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  scalarPairingOfMap M (exteriorDualPairing M)

lemma canonicalDeterminantPairing_eval (M : X.Modules)
    (U : X.Opens) (s : Γ(exteriorSquare X (dualSheaf M),U)) (t : Γ(exteriorSquare X M,U)) :
    (canonicalDeterminantPairing M).val.app (op U)
      (PullbackDual.tensorSheafPure X _ _ U (s ⊗ₜ[X.presheaf.obj (op U)] t)) =
    dualPairing (exteriorSquare X M) ((exteriorDualPairing M).val.app (op U) s) (Over.mk (𝟙 U)) t :=
  scalarPairingOfMap_eval M (exteriorDualPairing M) U s t
end NcCubic.Geometry.ImmersionBracketNaturality
