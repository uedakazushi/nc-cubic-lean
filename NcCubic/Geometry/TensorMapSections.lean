/- Canonical exterior/tensor comparison on actual local sections. -/
module
public import NcCubic.Geometry.ScalarPairingPullback
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
variable (X : RingedSpace.{u,u})
variable {A A' B B' : _root_.SheafOfModules.{u} (structureSheafRing X)}
/-- The actual bifunctor map; pure-tensor proof adapted from pinned Stacks
FlatSquareZeroThickening.tensorRight_map_tmul (Apache-2.0). -/
lemma tensorMapLeft_tmul (f : A ⟶ A') (B : _root_.SheafOfModules.{u} (structureSheafRing X))
    (U : TopologicalSpace.Opens X.carrier) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).map f).app B).val.app (op U)
      (toTensorSheafSection X A B (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b)) =
    toTensorSheafSection X A' B (op U) (f.val.app (op U) a ⊗ₜ[X.presheaf.obj (op U)] b) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)
  have hn := congrArg (fun k => k.app (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b))
    (adj.unit.naturality (PresheafOfModules.tensorHom (O := X.presheaf) f.val (𝟙 B.val))).symm
  change (((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).map f).app B).val.app (op U)
      (toTensorSheafSection X A B (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b)) =
    toTensorSheafSection X A' B (op U)
      ((PresheafOfModules.tensorHom (O := X.presheaf) f.val (𝟙 B.val)).app (op U)
        (a ⊗ₜ[X.presheaf.obj (op U)] b)) at hn
  exact hn.trans (congrArg (toTensorSheafSection X A' B (op U))
    (PresheafOfModules.tensorHom_tmul f.val (𝟙 B.val) (op U) a b))

/-- Adapted from pinned Stacks FlatSquareZeroThickening.tensorLeft_map_tmul (Apache-2.0). -/
lemma tensorMapRight_tmul (A : _root_.SheafOfModules.{u} (structureSheafRing X)) (g : B ⟶ B')
    (U : TopologicalSpace.Opens X.carrier) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj A).map g).val.app (op U)
      (toTensorSheafSection X A B (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b)) =
    toTensorSheafSection X A B' (op U) (a ⊗ₜ[X.presheaf.obj (op U)] g.val.app (op U) b) := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureSheafRing X).obj)
  have hn := congrArg (fun k => k.app (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b))
    (adj.unit.naturality (PresheafOfModules.tensorHom (O := X.presheaf) (𝟙 A.val) g.val)).symm
  change (((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj A).map g).val.app (op U)
      (toTensorSheafSection X A B (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b)) =
    toTensorSheafSection X A B' (op U)
      ((PresheafOfModules.tensorHom (O := X.presheaf) (𝟙 A.val) g.val).app (op U)
        (a ⊗ₜ[X.presheaf.obj (op U)] b)) at hn
  exact hn.trans (congrArg (toTensorSheafSection X A B' (op U))
    (PresheafOfModules.tensorHom_tmul (𝟙 A.val) g.val (op U) a b))

def tensorMap (f : A ⟶ A') (g : B ⟶ B') :
    ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj A).obj B ⟶
      ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj A').obj B' :=
  ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).map f).app B ≫
    ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj A').map g

lemma tensorMap_tmul (f : A ⟶ A') (g : B ⟶ B')
    (U : TopologicalSpace.Opens X.carrier) (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    (tensorMap X f g).val.app (op U)
      (toTensorSheafSection X A B (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b)) =
    toTensorSheafSection X A' B' (op U)
      (f.val.app (op U) a ⊗ₜ[X.presheaf.obj (op U)] g.val.app (op U) b) :=
  (congrArg ((((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj A').map g).val.app (op U))
    (tensorMapLeft_tmul X f B U a b)).trans
    (tensorMapRight_tmul X A' g U (f.val.app (op U) a) b)
end NcCubic.Geometry.ImmersionBracketNaturality
