module
public import NcCubic.Geometry.ExteriorDescentApply
@[expose] public noncomputable section
namespace NcCubic.Geometry.PresheafExterior
open CategoryTheory
universe u v w a
variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (n : ℕ)
def wedgeAlternating (U : Cᵒᵖ) :
    AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U) (F.obj U)
      ((PresheafOfModules.extPow (O:=O) n F).obj U) (Fin n) :=
  (PresheafOfModules.extPowSections n F U).symm.toLinearMap.compAlternatingMap
    (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj U) n)

theorem wedgeSection_map {U V : Cᵒᵖ} (h : U ⟶ V) (v : Fin n → F.obj U) :
    (PresheafOfModules.extPow (O:=O) n F).map h (wedgeSection F n U v) =
      wedgeSection F n V (fun i => F.map h (v i)) := by
  change ExteriorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map h).hom (F.restrictₛₗ h)
    (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj U) n v) = _
  rw [ExteriorAlgebra.powMapₛₗ_ιMulti]
  rfl
end NcCubic.Geometry.PresheafExterior
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{u}}
def exteriorWedgeAlternating (M : X.Modules) (U : X.Opens) :
    AlternatingMap Γ(X,U) Γ(M,U) Γ(Scheme.Modules.exteriorPower M (2:ℤ),U) (Fin 2) :=
  alternatingSemilinearTransport
    (((exteriorPresheafUnit M).app (op U)).hom.compAlternatingMap
      (PresheafExterior.wedgeAlternating (O:=X.sheaf.obj)
        (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X) M) 2 (op U)))
    (siteSectionSemilinearEquiv M U).symm.toLinearMap
    (siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) U).toLinearMap

theorem exteriorWedgeAlternating_eval (M : X.Modules) (U : X.Opens) (v : Fin 2 → Γ(M,U)) :
    exteriorWedgeAlternating M U v =
      siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) U
        (exteriorUnitWedge M U (fun i => (siteSectionSemilinearEquiv M U).symm (v i))) := rfl

theorem exteriorUnitWedge_map (M : X.Modules) {U V : X.Opens} (h : V ⟶ U)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp:=X.sheaf)
      (Opens.grothendieckTopology ↥X) M).obj (op U)) :
    (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
      (Scheme.Modules.exteriorPower M (2:ℤ))).map h.op (exteriorUnitWedge M U v) =
    exteriorUnitWedge M V (fun i => (SheafOfModules.valPresheaf (Osharp:=X.sheaf)
      (Opens.grothendieckTopology ↥X) M).map h.op (v i)) := by
  have hn := PresheafOfModules.naturality_apply (exteriorPresheafUnit M) h.op (exteriorRawWedge M U v)
  have hw := PresheafExterior.wedgeSection_map (O:=X.sheaf.obj)
    (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X) M) 2 h.op v
  exact hn.symm.trans (congrArg ((exteriorPresheafUnit M).app (op V)) hw)

theorem exteriorWedgeAlternating_raw (M : X.Modules) (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp:=X.sheaf)
      (Opens.grothendieckTopology ↥X) M).obj (op U)) :
    exteriorWedgeAlternating M U (fun i => siteSectionSemilinearEquiv M U (v i)) =
      siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) U (exteriorUnitWedge M U v) := by
  rw [exteriorWedgeAlternating_eval]
  exact congrArg (fun w => siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) U
    (exteriorUnitWedge M U w)) (funext fun i => (siteSectionSemilinearEquiv M U).symm_apply_apply (v i))

theorem exteriorWedgeAlternating_natural (M : X.Modules) {U V : X.Opens} (h : V ⟶ U)
    (v : Fin 2 → Γ(M,U)) :
    (Scheme.Modules.exteriorPower M (2:ℤ)).presheaf.map h.op (exteriorWedgeAlternating M U v) =
      exteriorWedgeAlternating M V (fun i => M.presheaf.map h.op (v i)) := by
  let vraw := fun i => (siteSectionSemilinearEquiv M U).symm (v i)
  calc
    _ = siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) V
        ((SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
          (Scheme.Modules.exteriorPower M (2:ℤ))).map h.op (exteriorUnitWedge M U vraw)) :=
      (siteSectionSemilinearEquiv_natural _ h _).symm
    _ = siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) V
        (exteriorUnitWedge M V (fun i => (SheafOfModules.valPresheaf (Osharp:=X.sheaf)
          (Opens.grothendieckTopology ↥X) M).map h.op (vraw i))) :=
      congrArg (siteSectionSemilinearEquiv _ V) (exteriorUnitWedge_map M h vraw)
    _ = exteriorWedgeAlternating M V (fun i => siteSectionSemilinearEquiv M V
        ((SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X) M).map h.op (vraw i))) :=
      (exteriorWedgeAlternating_raw M V _).symm
    _ = _ := congrArg (exteriorWedgeAlternating M V) (funext fun i =>
      (siteSectionSemilinearEquiv_natural M h (vraw i)).trans
        (congrArg (M.presheaf.map h.op) ((siteSectionSemilinearEquiv M U).apply_symm_apply (v i))))
end NcCubic.Geometry
