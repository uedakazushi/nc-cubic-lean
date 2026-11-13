/- The canonical identity comparison for exterior powers, before any
projective scheme or twisting sheaf is substituted. -/
module
public import NcCubic.Geometry.ModulesBridge
public import NcCubic.Geometry.ImmersionExterior
public import NcCubic.Geometry.SheafExteriorFrame
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace NcCubic.Geometry.ExteriorSiteNativeBridge
universe u
variable (X : Scheme.{u})

/-- Equality of the actual exterior objects under the identity site-to-scheme
comparison. It is checked with an abstract scheme, not a projective presentation. -/
theorem exterior_obj_eq
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    (schemeModulesOfSite X).obj
      ((_root_.SheafOfModules.algebras _ M).exteriorPower q) =
      Scheme.Modules.exteriorPower (X := X) ((schemeModulesOfSite X).obj M) (q : ℤ) := rfl

/-- The canonical site/native exterior comparison is transport by the actual
object equality; its underlying operation is the identity. -/
def exteriorIso
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (q : ℕ) :
    (schemeModulesOfSite X).obj
      ((_root_.SheafOfModules.algebras _ M).exteriorPower q) ≅
      Scheme.Modules.exteriorPower (X := X) ((schemeModulesOfSite X).obj M) (q : ℤ) :=
  eqToIso (exterior_obj_eq X M q)

local instance : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (_root_.SheafOfModules.{u} X.ringCatSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Finite coordinate sums also agree before exterior powers are taken. -/
theorem sum_obj_eq (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N : ℕ) :
    (schemeModulesOfSite X).obj (⨁ fun _ : Fin N => M) =
      SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N := rfl

def sumIso (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N : ℕ) :
    (schemeModulesOfSite X).obj (⨁ fun _ : Fin N => M) ≅
      SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N :=
  eqToIso (sum_obj_eq X M N)
/-- Cross both spelling boundaries canonically: first exterior powers, then
transport the finite coordinate sum through its generic object comparison. -/
def exteriorSumIso (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ) :
    (schemeModulesOfSite X).obj
      ((_root_.SheafOfModules.algebras _
        ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf)).exteriorPower q) ≅
      Scheme.Modules.exteriorPower (X := X)
        (SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N) (q : ℤ) :=
  exteriorIso X (⨁ fun _ : Fin N => M) q ≪≫
    (Scheme.Modules.exteriorPowerFunctor X (q : ℤ)).mapIso (sumIso X M N)
/-- The comparison retains the underlying identity on the exterior object. -/
theorem exteriorSumIso_hom_eq_id
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ) :
    (exteriorSumIso X M N q).hom =
      𝟙 (Scheme.Modules.exteriorPower (X := X)
        (SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N) (q : ℤ)) := by
  simp [exteriorSumIso, exteriorIso, sumIso]
  rfl

/-- Coordinate wedge components retain their value after the canonical
site/native comparison. All conversions are checked for an abstract scheme. -/
theorem component_comp_exteriorSumIso
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N : ℕ) (i j : Fin N) :
    (SheafExteriorFrame.component (X := X) ((schemeModulesOfSite X).obj M) N i j :
      SheafExteriorFrame.tensorSquare (X := X) ((schemeModulesOfSite X).obj M) ⟶
      (schemeModulesOfSite X).obj
        ((_root_.SheafOfModules.algebras _
          ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf)).exteriorPower 2)) ≫
      (exteriorSumIso X M N 2).hom =
      SheafExteriorFrame.component (X := X) ((schemeModulesOfSite X).obj M) N i j := by
  rw [exteriorSumIso_hom_eq_id]
  exact Category.comp_id _
/-- The comparison can be inserted before any native exterior map without
changing that map. This equality is checked before any scheme is instantiated. -/
theorem exteriorSumIso_hom_comp_exteriorPowerMap
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {T : X.Modules}
    (g : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ⟶ T) :
    (exteriorSumIso X M N q).hom ≫ Scheme.Modules.exteriorPowerMap (X := X) g (q : ℤ) =
      Scheme.Modules.exteriorPowerMap (X := X) g (q : ℤ) := by
  rw [exteriorSumIso_hom_eq_id]
  exact Category.id_comp _
/-- Every local component value is unchanged under the canonical comparison. -/
theorem exteriorSumIso_component_apply
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N : ℕ) (i j : Fin N)
    (U : X.Opensᵒᵖ)
    (t : (SheafExteriorFrame.tensorSquare (X := X) ((schemeModulesOfSite X).obj M)).val.obj U) :
    (exteriorSumIso X M N 2).hom.val.app U
      ((SheafExteriorFrame.component (X := X) ((schemeModulesOfSite X).obj M) N i j).val.app U t) =
      (SheafExteriorFrame.component (X := X) ((schemeModulesOfSite X).obj M) N i j).val.app U t := by
  exact congrArg (fun f :
    SheafExteriorFrame.tensorSquare (X := X) ((schemeModulesOfSite X).obj M) ⟶
      Scheme.Modules.exteriorPower (X := X)
        (SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N) 2 =>
      f.val.app U t) (component_comp_exteriorSumIso X M N i j)
/-- Transport a native section of the raw site sum into its lower exterior
power, then through the native coordinate sum. The resulting exterior map is
exactly the exterior map of the explicitly transported original arrow. -/
theorem transported_exterior_map
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {T : X.Modules}
    (g : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ⟶ T) :
    (exteriorIso X
      ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf) q).inv ≫
      (exteriorSumIso X M N q).hom ≫
        Scheme.Modules.exteriorPowerMap (X := X) g (q : ℤ) =
      Scheme.Modules.exteriorPowerMap (X := X) ((sumIso X M N).hom ≫ g) (q : ℤ) := by
  simp only [exteriorSumIso, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact (Scheme.Modules.exteriorPowerMap_comp (X := X) (sumIso X M N).hom g (q : ℤ)).symm

/-- The same canonical transport identity evaluated on an actual local
section. Every source and every section carrier is fixed at abstract `X`. -/
theorem transported_exterior_map_apply
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {T : X.Modules}
    (g : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ⟶ T)
    (U : X.Opensᵒᵖ)
    (σ : (Scheme.Modules.exteriorPower (X := X)
      ((schemeModulesOfSite X).obj
        ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf)) (q : ℤ)).val.obj U) :
    (Scheme.Modules.exteriorPowerMap (X := X) g (q : ℤ)).val.app U
      ((exteriorSumIso X M N q).hom.val.app U
        ((exteriorIso X
          ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf) q).inv.val.app U σ)) =
      (Scheme.Modules.exteriorPowerMap (X := X) ((sumIso X M N).hom ≫ g) (q : ℤ)).val.app U σ := by
  exact congrArg (fun f :
    Scheme.Modules.exteriorPower (X := X)
      ((schemeModulesOfSite X).obj
        ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf)) (q : ℤ) ⟶
      Scheme.Modules.exteriorPower (X := X) T (q : ℤ) => f.val.app U σ)
    (transported_exterior_map X M N q g)
/-- Direct application of the buffered composite, avoiding a caller-side
conversion from composite application to nested application. -/
theorem transported_exterior_composite_apply
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {T : X.Modules}
    (g : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ⟶ T)
    (U : X.Opensᵒᵖ)
    (σ : (Scheme.Modules.exteriorPower (X := X)
      ((schemeModulesOfSite X).obj
        ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf)) (q : ℤ)).val.obj U) :
    ((exteriorSumIso X M N q).hom ≫
      Scheme.Modules.exteriorPowerMap (X := X) g (q : ℤ)).val.app U
        ((exteriorIso X
          ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf) q).inv.val.app U σ) =
      (Scheme.Modules.exteriorPowerMap (X := X) ((sumIso X M N).hom ≫ g) (q : ℤ)).val.app U σ := by
  exact transported_exterior_map_apply X M N q g U σ

/-- The same formula with an isomorphism followed by a map. This retains the
literal composite isomorphism appearing in the original Euler lift. -/
theorem transported_exterior_composite_iso_apply
    (M : _root_.SheafOfModules.{u} X.ringCatSheaf) (N q : ℕ)
    {D T : X.Modules}
    (e : SheafExteriorFrame.sum (X := X) ((schemeModulesOfSite X).obj M) N ≅ D)
    (h : D ⟶ T)
    (U : X.Opensᵒᵖ)
    (σ : (Scheme.Modules.exteriorPower (X := X)
      ((schemeModulesOfSite X).obj
        ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf)) (q : ℤ)).val.obj U) :
    ((exteriorSumIso X M N q).hom ≫
      Scheme.Modules.exteriorPowerMap (X := X) (e.hom ≫ h) (q : ℤ)).val.app U
        ((exteriorIso X
          ((⨁ fun _ : Fin N => M) : _root_.SheafOfModules.{u} X.ringCatSheaf) q).inv.val.app U σ) =
      (Scheme.Modules.exteriorPowerMap (X := X) ((sumIso X M N ≪≫ e).hom ≫ h) (q : ℤ)).val.app U σ := by
  simpa only [Iso.trans_hom, Category.assoc] using
    transported_exterior_composite_apply X M N q (e.hom ≫ h) U σ

end NcCubic.Geometry.ExteriorSiteNativeBridge
