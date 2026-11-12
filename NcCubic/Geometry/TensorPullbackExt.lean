/- Pure-unit tests for actual pulled-back tensor morphisms, via adjunction. -/
module
public import NcCubic.Geometry.PullbackDual
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
lemma tensor_hom_ext (X : RingedSpace.{u,u})
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X))
    (a b : ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj F).obj G ⟶ H)
    (h : ∀ U (f : F.val.obj (op U)) (g : G.val.obj (op U)),
      a.val.app (op U) (toTensorSheafSection X F G (op U) (f ⊗ₜ[X.presheaf.obj (op U)] g)) =
      b.val.app (op U) (toTensorSheafSection X F G (op U) (f ⊗ₜ[X.presheaf.obj (op U)] g))) : a = b := by
  let e := PresheafOfModules.sheafificationHomEquiv
    (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)
    (P := PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) (F := H)
  apply e.injective
  have he (c : ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj F).obj G ⟶ H) :
      e c = sheafifyUnit X (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) ≫ c.val :=
    (PresheafOfModules.sheafificationAdjunction
      (R := structureSheafRing X) (𝟙 (structureSheafRing X).obj)).homEquiv_unit
      (PresheafOfModules.tensorObj (O := X.presheaf) F.val G.val) H c
  rw [he a,he b]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  exact h U.unop f g
private lemma iso_hom_cancel {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f g : B ⟶ D) (h : e.hom ≫ f = e.hom ≫ g) : f = g := by
  exact (cancel_epi e.hom).mp h

lemma pullback_tensor_hom_ext {X P : Scheme.{u}} (i : X ⟶ P)
    (A B : P.Modules) (H : X.Modules)
    (f g : (((Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,X.toRingedSpace.IsSheaf⟩).obj
      ((Scheme.Modules.pullback i).obj A)).obj ((Scheme.Modules.pullback i).obj B)) ⟶ H)
    (h : ∀ U (a : Γ(A,U)) (b : Γ(B,U)),
      f.val.app (op (i ⁻¹ᵁ U))
        (PullbackDual.tensorSheafPure X ((Scheme.Modules.pullback i).obj A)
          ((Scheme.Modules.pullback i).obj B) (i ⁻¹ᵁ U)
          ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A).val.app (op U) a)
            ⊗ₜ[X.presheaf.obj (op (i ⁻¹ᵁ U))]
          (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B).val.app (op U) b))) =
      g.val.app (op (i ⁻¹ᵁ U))
        (PullbackDual.tensorSheafPure X ((Scheme.Modules.pullback i).obj A)
          ((Scheme.Modules.pullback i).obj B) (i ⁻¹ᵁ U)
          ((((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A).val.app (op U) a)
            ⊗ₜ[X.presheaf.obj (op (i ⁻¹ᵁ U))]
          (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app B).val.app (op U) b)))) : f = g := by
  let e := PullbackDual.pullbackTensorIso i A B
  apply iso_hom_cancel e f g
  apply ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ H).injective
  apply tensor_hom_ext P.toRingedSpace A B ((Scheme.Modules.pushforward i).obj H)
  intro U a b
  change f.val.app (op (i ⁻¹ᵁ U)) (e.hom.val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _).val.app (op U)
        (PullbackDual.tensorSheafPure P A B U (a ⊗ₜ[P.presheaf.obj (op U)] b)))) =
    g.val.app (op (i ⁻¹ᵁ U)) (e.hom.val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _).val.app (op U)
        (PullbackDual.tensorSheafPure P A B U (a ⊗ₜ[P.presheaf.obj (op U)] b))))
  have ht := PullbackDual.comparison_tensorSheafPure i A B U a b
  exact (congrArg (f.val.app (op (i ⁻¹ᵁ U))) ht).trans
    ((h U a b).trans (congrArg (g.val.app (op (i ⁻¹ᵁ U))) ht).symm)
end NcCubic.Geometry.ImmersionBracketNaturality
