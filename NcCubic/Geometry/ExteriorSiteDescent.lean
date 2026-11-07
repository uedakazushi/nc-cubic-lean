/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.PresheafExteriorDesc
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import Mathlib.CategoryTheory.Adjunction.Additive
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {O : Sheaf J CommRingCat.{w}}
set_option backward.isDefEq.respectTransparency false in
/-- The actual exterior universal descent on any site, including a scheme's slice sites. -/
def descendExteriorOnSite (F G : SheafOfModules.{w} (Sheaf.toRingCat J O)) (n : ℕ)
    (α : PresheafOfModules.extPow (O := O.obj) n (SheafOfModules.valPresheaf J F) ⟶
      SheafOfModules.valPresheaf J G) :
    (SheafOfModules.algebras J F).exteriorPower n ⟶ G :=
  (SheafOfModules.exteriorPowerSheafifyIso J (SheafOfModules.algebras J F) n).hom ≫
    (PresheafOfModules.moduleSheafification J (𝟙 O.obj)).map α ≫
      (SheafOfModules.sheafifyValIso J G).hom

/-- The full universal property: every actual exterior-sheaf morphism is uniquely
represented by a compatible sectionwise exterior morphism. -/
def exteriorSiteHomEquiv (F G : SheafOfModules.{w} (Sheaf.toRingCat J O)) (n : ℕ) :
    (PresheafOfModules.extPow (O := O.obj) n (SheafOfModules.valPresheaf J F) ⟶
      SheafOfModules.valPresheaf J G) ≃
    ((SheafOfModules.algebras J F).exteriorPower n ⟶ G) :=
  ((PresheafOfModules.sheafificationAdjunction (J := J) (Sheaf.toRingCatMap J (𝟙 O.obj))).homEquiv _ G).symm.trans
    (Iso.homCongr (SheafOfModules.exteriorPowerSheafifyIso J
      (SheafOfModules.algebras J F) n).symm (Iso.refl G))


theorem exteriorSiteHomEquiv_eq_desc (F G : SheafOfModules.{w} (Sheaf.toRingCat J O)) (n : ℕ)
    (α : PresheafOfModules.extPow (O := O.obj) n (SheafOfModules.valPresheaf J F) ⟶
      SheafOfModules.valPresheaf J G) :
    exteriorSiteHomEquiv J F G n α = descendExteriorOnSite J F G n α := by
  rfl

theorem exteriorSiteHomEquiv_add (F G : SheafOfModules.{w} (Sheaf.toRingCat J O)) (n : ℕ)
    (α β : PresheafOfModules.extPow (O := O.obj) n (SheafOfModules.valPresheaf J F) ⟶
      SheafOfModules.valPresheaf J G) :
    exteriorSiteHomEquiv J F G n (α+β) =
      exteriorSiteHomEquiv J F G n α + exteriorSiteHomEquiv J F G n β := by
  let adj := PresheafOfModules.sheafificationAdjunction (J := J)
    (Sheaf.toRingCatMap J (𝟙 O.obj))
  let : (SheafOfModules.forget (Sheaf.toRingCat J O) ⋙
    PresheafOfModules.restrictScalars (Sheaf.toRingCatMap J (𝟙 O.obj))).Additive :=
    ⟨by intros; rfl⟩
  let := adj.left_adjoint_additive
  let e := SheafOfModules.exteriorPowerSheafifyIso J (SheafOfModules.algebras J F) n
  change e.hom ≫ (adj.homEquiv _ G).symm (α+β) =
    (e.hom ≫ (adj.homEquiv _ G).symm α)+(e.hom ≫ (adj.homEquiv _ G).symm β)
  exact (congrArg (fun k => e.hom ≫ k) (adj.homAddEquiv_symm_add _ G α β)).trans
    (Preadditive.comp_add _ _ _ _ _ _)
end NcCubic.Geometry
