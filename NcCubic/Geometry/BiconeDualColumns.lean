module
public import StacksFrontier.AlgebraicGeometry.Modules.DualBiproduct
public import NcCubic.Geometry.ModulesBridge
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
namespace NcCubic.Geometry.CanonicalEulerMiddle
universe u v w

/-- Relabel a bicone by explicit pointwise isomorphisms, without choosing a
new coproduct vertex. -/
def relabelBicone {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {I : Type w} {F G : I → C} (b : Bicone F) (e : ∀ i, G i ≅ F i) : Bicone G where
  pt := b.pt
  π i := b.π i ≫ (e i).inv
  ι i := (e i).hom ≫ b.ι i
  ι_π i j := by
    classical
    by_cases h : i = j
    · subst j
      simp [Category.assoc]
    · simp only [h, dite_false]
      calc
        _ = (e i).hom ≫ (b.ι i ≫ b.π j) ≫ (e j).inv := by simp only [Category.assoc]
        _ = 0 := by rw [bicone_ι_π_ne b h]; simp

/-- Bilimitness is preserved by a pointwise isomorphism of the family. -/
def relabelBicone_isBilimit {C : Type u} [Category.{v} C] [Preadditive C]
    {I : Type w} [Finite I] {F G : I → C} (b : Bicone F) (hb : b.IsBilimit)
    (e : ∀ i, G i ≅ F i) : (relabelBicone b e).IsBilimit := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  apply isBilimitOfTotal
  calc
    ∑ i : I, (relabelBicone b e).π i ≫ (relabelBicone b e).ι i =
        ∑ i : I, b.π i ≫ b.ι i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [relabelBicone, Category.assoc, Iso.inv_hom_id_assoc]
    _ = 𝟙 b.pt := IsBilimit.total hb

/-- Two actual bilimit bicones are compared directly through their original
inclusions; no intermediate chosen biproduct is introduced. -/
def biconeComparisonIso {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {I : Type w} {F : I → C} (b c : Bicone F) (hb : b.IsBilimit) (hc : c.IsBilimit) :
    b.pt ≅ c.pt where
  hom := hb.isColimit.desc c.toCocone
  inv := hc.isColimit.desc b.toCocone
  hom_inv_id := by
    apply hb.isColimit.hom_ext
    intro j
    rw [← Category.assoc, hb.isColimit.fac, hc.isColimit.fac]
    exact (Category.comp_id (b.toCocone.ι.app j)).symm
  inv_hom_id := by
    apply hc.isColimit.hom_ext
    intro j
    rw [← Category.assoc, hc.isColimit.fac, hb.isColimit.fac]
    exact (Category.comp_id (c.toCocone.ι.app j)).symm

@[simp] theorem biconeComparisonIso_column
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    {I : Type w} {F : I → C} (b c : Bicone F) (hb : b.IsBilimit) (hc : c.IsBilimit) (i : I) :
    b.ι i ≫ (biconeComparisonIso b c hb hc).hom = c.ι i :=
  hb.isColimit.fac c.toCocone (Discrete.mk i)

open Stacks.AlgebraicGeometry.ReflexiveModules

/-- Canonical comparison with the dual of an ORIGINAL bicone, using only
its dual bicone and the specified pointwise duality maps. -/
def dualBiconeComparisonIso (X : Scheme.{u}) {I : Type v} [Finite I]
    {F G : I → X.Modules} (b : Bicone F) (c : Bicone G)
    (hb : b.IsBilimit) (hc : c.IsBilimit) (e : ∀ i, G i ≅ dualSheaf (X := X) (F i)) :
    c.pt ≅ dualSheaf (X := X) b.pt :=
  biconeComparisonIso c (relabelBicone (dualBicone (X := X) b) e) hc
    (relabelBicone_isBilimit (dualBicone (X := X) b) (dualBicone_isBilimit (X := X) b hb) e)

@[simp] theorem dualBiconeComparisonIso_column (X : Scheme.{u}) {I : Type v} [Finite I]
    {F G : I → X.Modules} (b : Bicone F) (c : Bicone G)
    (hb : b.IsBilimit) (hc : c.IsBilimit) (e : ∀ i, G i ≅ dualSheaf (X := X) (F i)) (i : I) :
    c.ι i ≫ (dualBiconeComparisonIso X b c hb hc e).hom =
      (e i).hom ≫ dualMap (X := X) (b.π i) :=
  biconeComparisonIso_column c (relabelBicone (dualBicone (X := X) b) e) hc
    (relabelBicone_isBilimit (dualBicone (X := X) b) (dualBicone_isBilimit (X := X) b hb) e) i

/-- The identity site/scheme comparison preserves an ORIGINAL bicone and
its bilimit structure, without choosing any new native biproduct vertex. -/
def mapSiteBicone_isBilimit (X : Scheme.{u}) {I : Type v} [Finite I]
    {F : I → _root_.SheafOfModules.{u} X.ringCatSheaf}
    (b : Bicone F) (hb : b.IsBilimit) :
    ((schemeModulesOfSite X).mapBicone b).IsBilimit := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI : PreservesBiproductsOfShape I (schemeModulesOfSite X) :=
    preservesBiproductsOfShape_of_preservesProductsOfShape _
  exact isBilimitOfPreserves (schemeModulesOfSite X) hb

end NcCubic.Geometry.CanonicalEulerMiddle
