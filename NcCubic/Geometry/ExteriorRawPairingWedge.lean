module
public import NcCubic.Geometry.ExteriorRawPairing
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
theorem nativeModuleHom_app_apply {X : Scheme.{u}} {F G : X.Modules}
    (g : F ⟶ G) (U : X.Opens) (x : Γ(F,U)) :
    g.app U x = g.val.app (op U) x := rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
theorem exteriorRawPairing_native_wedge {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (v : Fin 2 → Γ(dualSheaf M,U)) :
    (exteriorRawPairing M).app U (exteriorWedgeAlternating (dualSheaf M) U v) =
      localRawExteriorPairing M (v 0) (v 1) := by
  rw [nativeModuleHom_app_apply, exteriorWedgeAlternating_eval]
  let w := fun i => (siteSectionSemilinearEquiv (dualSheaf M) U).symm (v i)
  let α := exteriorRawPairingPresheaf M
  have hα :=
    PresheafExterior.desc_wedgeSection.{u,u,u,u} (O := X.sheaf.obj)
      (G := SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (exteriorRawDualSheaf M))
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (dualSheaf M)) 2
      (fun W => exteriorRawPairingAlternating M W.unop)
      (fun h v => exteriorRawPairingAlternating_natural M h.unop v) (op U) w
  have hraw := (exteriorUnitWedge_descend (dualSheaf M) (exteriorRawDualSheaf M) α U w).trans hα
  have hsite := siteSectionSemilinearEquiv_map (exteriorRawPairing M) U
    (exteriorUnitWedge (dualSheaf M) U w)
  have hm := hsite.symm.trans ((congrArg (siteSectionSemilinearEquiv (exteriorRawDualSheaf M) U)
    hraw).trans (exteriorRawPairingAlternating_eval M U w))
  have hv : (fun i => siteSectionSemilinearEquiv (dualSheaf M) U (w i)) = v :=
    funext fun i => (siteSectionSemilinearEquiv (dualSheaf M) U).apply_symm_apply (v i)
  exact hm.trans (congrArg (localRawExteriorPairingVector M U) hv)

set_option backward.isDefEq.respectTransparency false in
theorem exteriorDualPairing_toRaw {X : Scheme.{u}} (M : X.Modules) :
    exteriorDualPairing M ≫ exteriorDualToRaw M = exteriorRawPairing M := by
  simp only [exteriorDualPairing, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem exteriorDualPairing_toRaw_native_wedge {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (v : Fin 2 → Γ(dualSheaf M,U)) :
    (exteriorDualToRaw M).app U
      ((exteriorDualPairing M).app U (exteriorWedgeAlternating (dualSheaf M) U v)) =
      localRawExteriorPairing M (v 0) (v 1) := by
  have h := congrArg (fun g : Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ) ⟶
      exteriorRawDualSheaf M => g.app U (exteriorWedgeAlternating (dualSheaf M) U v))
    (exteriorDualPairing_toRaw M)
  exact h.trans (exteriorRawPairing_native_wedge M U v)
end NcCubic.Geometry
