module
public import NcCubic.Geometry.ExteriorRawPairingLinear
public import NcCubic.Geometry.ExteriorRawDualIso
public import NcCubic.Geometry.ExteriorDescentApply
public import NcCubic.Geometry.ExteriorWedgeLaws
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
def localRawExteriorPairingVector {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (v : Fin 2 → Γ(dualSheaf M,U)) : Γ(exteriorRawDualSheaf M,U) :=
  localRawExteriorPairing M (v 0) (v 1)

set_option backward.isDefEq.respectTransparency false in
def exteriorRawPairingAlternating {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    AlternatingMap ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (dualSheaf M)).obj (op U))
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (exteriorRawDualSheaf M)).obj (op U)) (Fin 2) :=
  alternatingSemilinearTransport (localRawExteriorAlternating M U)
    (siteSectionSemilinearEquiv (dualSheaf M) U).toLinearMap
    (siteSectionSemilinearEquiv (exteriorRawDualSheaf M) U).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
theorem exteriorRawPairingAlternating_eval {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (dualSheaf M)).obj (op U)) :
    siteSectionSemilinearEquiv (exteriorRawDualSheaf M) U
      (exteriorRawPairingAlternating M U v) =
      localRawExteriorPairingVector M U
        (fun i => siteSectionSemilinearEquiv (dualSheaf M) U (v i)) :=
  (siteSectionSemilinearEquiv (exteriorRawDualSheaf M) U).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
theorem localRawExteriorPairingVector_natural {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ⟶ U) (v : Fin 2 → Γ(dualSheaf M,U)) :
    (exteriorRawDualSheaf M).presheaf.map h.op (localRawExteriorPairingVector M U v) =
      localRawExteriorPairingVector M V (fun i => (dualSheaf M).presheaf.map h.op (v i)) := by
  have hh : homOfLE (leOfHom h) = h := Subsingleton.elim _ _
  simpa only [localRawExteriorPairingVector, hh] using
    localRawExteriorPairing_restrict M (leOfHom h) (v 0) (v 1)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem exteriorRawPairingAlternating_natural {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ⟶ U)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (dualSheaf M)).obj (op U)) :
    (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (exteriorRawDualSheaf M)).map h.op (exteriorRawPairingAlternating M U v) =
      exteriorRawPairingAlternating M V (fun i =>
        (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
          (dualSheaf M)).map h.op (v i)) := by
  apply (siteSectionSemilinearEquiv (exteriorRawDualSheaf M) V).injective
  calc
    _ = (exteriorRawDualSheaf M).presheaf.map h.op
      (siteSectionSemilinearEquiv (exteriorRawDualSheaf M) U
        (exteriorRawPairingAlternating M U v)) := siteSectionSemilinearEquiv_natural _ h _
    _ = (exteriorRawDualSheaf M).presheaf.map h.op
      (localRawExteriorPairingVector M U
        (fun i => siteSectionSemilinearEquiv (dualSheaf M) U (v i))) :=
      congrArg _ (exteriorRawPairingAlternating_eval M U v)
    _ = localRawExteriorPairingVector M V (fun i => (dualSheaf M).presheaf.map h.op
      (siteSectionSemilinearEquiv (dualSheaf M) U (v i))) :=
      localRawExteriorPairingVector_natural M h _
    _ = localRawExteriorPairingVector M V (fun i => siteSectionSemilinearEquiv (dualSheaf M) V
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (dualSheaf M)).map h.op (v i))) :=
      congrArg (localRawExteriorPairingVector M V)
        (funext fun i => (siteSectionSemilinearEquiv_natural (dualSheaf M) h (v i)).symm)
    _ = _ := (exteriorRawPairingAlternating_eval M V _).symm

set_option backward.isDefEq.respectTransparency false in
def exteriorRawPairingPresheaf {X : Scheme.{u}} (M : X.Modules) :
    PresheafOfModules.extPow.{u,u,u,u} (O := X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (dualSheaf M)) ⟶
    SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (exteriorRawDualSheaf M) :=
  PresheafExterior.desc (O := X.sheaf.obj)
    (fun U => exteriorRawPairingAlternating M U.unop)
    (fun h v => exteriorRawPairingAlternating_natural M h.unop v)

set_option backward.isDefEq.respectTransparency false in
def exteriorRawPairing {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ) ⟶ exteriorRawDualSheaf M :=
  descendExteriorPresheafMorphism (dualSheaf M) (exteriorRawDualSheaf M)
    (exteriorRawPairingPresheaf M)

set_option backward.isDefEq.respectTransparency false in
def exteriorDualPairing {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ) ⟶
      dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)) :=
  exteriorRawPairing M ≫ inv (exteriorDualToRaw M)
end NcCubic.Geometry
