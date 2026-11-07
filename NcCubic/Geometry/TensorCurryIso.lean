/- Canonical currying of an actual perfect sheaf pairing is an isomorphism.
The forward map is the literal sheafification/presheaf tensor-Hom curry; an
adjunction equivalence certifies invertibility without choosing that map by
an abstract inverse-object isomorphism. -/
module
public import NcCubic.Geometry.SheafTensorCurry
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Opposite TopologicalSpace
universe u
namespace NcCubic.Geometry.CanonicalTwistDuality
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.SheafOfModules
lemma curry_eq_adjunction (X : RingedSpace.{u,u})
    (F G H : _root_.SheafOfModules.{u} (structureSheafRing X))
    (t : ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj F).obj G ⟶ H) :
    SheafTensorCurry.tensorHomEquiv X F G H t =
      (InternalHom.sheafTensorRightHomAdjunction ⟨X.presheaf,X.IsSheaf⟩ G).homEquiv F H t := by
  simp only [SheafTensorCurry.tensorHomEquiv, InternalHom.sheafTensorRightHomAdjunction,
    Adjunction.restrictFullyFaithful, Adjunction.mkOfHomEquiv_homEquiv,
    Adjunction.comp, Adjunction.mk'_homEquiv,
    InternalHom.sheafifyForgetAdjunction,
    Stacks.PresheafOfModules.InternalHom.presheafTensorHomEquiv]
  rfl

lemma homEquiv_isIso_of_equivalence {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.IsEquivalence]
    {A : C} {B : D} (t : L.obj A ⟶ B) (ht : IsIso t) : IsIso (adj.homEquiv A B t) := by
  have := ht
  rw [Adjunction.homEquiv_unit]
  infer_instance

lemma isIso_curry_of_pairingIso (X : RingedSpace.{u,u})
    (F G : _root_.SheafOfModules.{u} (structureSheafRing X))
    (e : ((Tensor.sheafTensor ⟨X.presheaf,X.IsSheaf⟩).obj F).obj G ≅
      SheafOfModules.unit (structureSheafRing X)) :
    IsIso (SheafTensorCurry.tensorHomEquiv X F G
      (SheafOfModules.unit (structureSheafRing X)) e.hom) := by
  let R : Sheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u} := ⟨X.presheaf,X.IsSheaf⟩
  let : MonoidalCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    _root_.SheafOfModules.monoidalCategorySheafTensor R
  let : SymmetricCategory (_root_.SheafOfModules.{u} (structureSheafRing X)) :=
    _root_.SheafOfModules.symmetricCategorySheafTensor R
  let hInv : HasInverse G :=
    { inv := F, isoLeft := (β_ G F) ≪≫ e, isoRight := e }
  let : ((Tensor.sheafTensor R).flip.obj G).IsEquivalence :=
    hInv.tensorRightEquivalence.isEquivalence_functor
  rw [curry_eq_adjunction]
  exact homEquiv_isIso_of_equivalence (InternalHom.sheafTensorRightHomAdjunction R G) e.hom (Iso.isIso_hom e)

end NcCubic.Geometry.CanonicalTwistDuality
