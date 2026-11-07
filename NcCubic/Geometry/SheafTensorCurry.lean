/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Focused currying readout adapted from the pinned AxiomMath/Stacks
Topology/Sheaves/Modules/TensorAndDuals/InternalHom.lean at
5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache-2.0).
Currying is obtained directly from the elementary sheafification/presheaf Hom
equivalence, without the general internal-Hom tensor isomorphism module.
-/
module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorHomAdjunction
@[expose] public section
open CategoryTheory TensorProduct Opposite TopologicalSpace
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.PresheafOfModules.InternalHom
universe u
namespace NcCubic.Geometry.SheafTensorCurry
variable (X : AlgebraicGeometry.RingedSpace.{u,u})
variable {F G H : _root_.SheafOfModules.{u} (structureSheafRing X)}
/-- The sheaf-hom `ℋom_{𝒪_X}(F, G)` of two sheaves of modules on a ringed space: the
sheaf-hom over the structure sheaf of the space. -/
noncomputable abbrev sheafHomSpace (X : AlgebraicGeometry.RingedSpace.{u, u})
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    _root_.SheafOfModules.{u} (structureSheafRing X) :=
  _root_.Stacks.SheafOfModules.sheafHom X.presheaf (structureSheafRing X).property F G

/-- Evaluation of a local section of an iterated sheaf-hom on two local sections. -/
noncomputable def evalNestedInternalHomSection
    (U : Opens X.carrier)
    (q : (sheafHomSpace X F (sheafHomSpace X G H)).val.obj (op U))
    (f : F.val.obj (op U)) (g : G.val.obj (op U)) : H.val.obj (op U) :=
  ((((q.app (op (Over.mk (𝟙 U)))).hom f).app (op (Over.mk (𝟙 U)))).hom g)

/-- Evaluation of a local morphism out of a tensor product on a local pure tensor. -/
noncomputable def evalTensorHomSection
    (U : Opens X.carrier)
    (s : (sheafHomSpace X
      (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G) H).val.obj (op U))
    (f : F.val.obj (op U)) (g : G.val.obj (op U)) : H.val.obj (op U) :=
  (s.app (op (Over.mk (𝟙 U)))).hom
    (toTensorSheafSection X F G (op U) (f ⊗ₜ[X.presheaf.obj (op U)] g))

/-- A morphism `F ⟶ ℋom(G, H)` is the curry of a morphism `F ⊗ G ⟶ H` when their
evaluations agree on every local pure tensor. -/
def IsTensorCurry (t : ((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H)
    (c : F ⟶ sheafHomSpace X G H) : Prop :=
  ∀ (U : Opens X.carrier) (f : F.val.obj (op U)) (g : G.val.obj (op U)),
    (((c.val.app (op U) f).app (op (Over.mk (𝟙 U)))).hom g) =
      t.val.app (op U)
        (toTensorSheafSection X F G (op U) (f ⊗ₜ[X.presheaf.obj (op U)] g))


noncomputable def tensorHomEquiv
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    (((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H) ≃ (F ⟶ sheafHomSpace X G H) :=
  (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).trans
    ((presheafTensorHomEquiv X.presheaf F.val G.val H.val).trans
      { toFun := fun f ↦ ⟨f⟩
        invFun := fun f ↦ f.val
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl })

/-- The forward direction of `tensorHomEquiv` is the canonical currying map. -/
@[stacks 01CN "morphism equivalence characterization"]
theorem tensorHomEquiv_isTensorCurry
    (t : ((Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj G ⟶ H) :
    IsTensorCurry X t (tensorHomEquiv X F G H t) := by
  intro U f g
  have h := presheafTensorHomEquiv_apply X.presheaf F.val G.val H.val
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t)
    U f (𝟙 U) g
  change (((tensorHomEquiv X F G H t).val.app (op U) f).app
      (op (Over.mk (𝟙 U)))).hom g =
    (PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t).app (op U)
      ((F.val.map (𝟙 (op U))) f ⊗ₜ[X.presheaf.obj (op U)] g) at h
  rw [PresheafOfModules.map_id] at h
  have hb := (PresheafOfModules.sheafificationAdjunction
    (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).homEquiv_unit
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) H t
  change PresheafOfModules.sheafificationHomEquiv
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj) t =
    sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) ≫ t.val at hb
  rwa [hb] at h


end NcCubic.Geometry.SheafTensorCurry
