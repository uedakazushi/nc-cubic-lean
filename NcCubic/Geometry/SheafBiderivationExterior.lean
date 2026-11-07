module
public import NcCubic.Geometry.SheafBiderivationPairing
public import NcCubic.Geometry.ExteriorDescentApply
public import NcCubic.Geometry.PresheafExteriorDesc
public import NcCubic.Geometry.LocalHomFamily
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (B : StructureSheafBiderivation X) (hR : B.IsRelative f)

set_option backward.isDefEq.respectTransparency false in
def biderivationRawAlternating (U : X.Opens) :
    AlternatingMap ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
      ((SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
        (Scheme.Hom.relativeDifferentials f)).obj (op U))
      ((SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
        (SheafOfModules.unit (structureSheaf X.sheaf))).obj (op U)) (Fin 2) :=
  alternatingSemilinearTransport (biderivationAlternating f B hR U)
    (siteSectionSemilinearEquiv (Scheme.Hom.relativeDifferentials f) U).toLinearMap
    (siteSectionSemilinearEquiv (SheafOfModules.unit (structureSheaf X.sheaf)) U).symm.toLinearMap

set_option backward.isDefEq.respectTransparency false in
theorem biderivationRawAlternating_eval (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
      (Scheme.Hom.relativeDifferentials f)).obj (op U)) :
    siteSectionSemilinearEquiv (SheafOfModules.unit (structureSheaf X.sheaf)) U
      (biderivationRawAlternating f B hR U v) =
      biderivationAlternating f B hR U
        (fun i => siteSectionSemilinearEquiv (Scheme.Hom.relativeDifferentials f) U (v i)) :=
  (siteSectionSemilinearEquiv (SheafOfModules.unit (structureSheaf X.sheaf)) U).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
theorem biderivationRawAlternating_natural {U V : X.Opens} (h : V ⟶ U)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
      (Scheme.Hom.relativeDifferentials f)).obj (op U)) :
    (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
      (SheafOfModules.unit (structureSheaf X.sheaf))).map h.op
        (biderivationRawAlternating f B hR U v) =
    biderivationRawAlternating f B hR V (fun i =>
      (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
        (Scheme.Hom.relativeDifferentials f)).map h.op (v i)) := by
  apply (siteSectionSemilinearEquiv (SheafOfModules.unit (structureSheaf X.sheaf)) V).injective
  calc
    _ = X.presheaf.map h.op
        (siteSectionSemilinearEquiv (SheafOfModules.unit (structureSheaf X.sheaf)) U
          (biderivationRawAlternating f B hR U v)) := siteSectionSemilinearEquiv_natural _ h _
    _ = X.presheaf.map h.op
        (biderivationAlternating f B hR U (fun i => siteSectionSemilinearEquiv (Scheme.Hom.relativeDifferentials f) U (v i))) :=
      congrArg _ (biderivationRawAlternating_eval f B hR U v)
    _ = biderivationAlternating f B hR V (fun i =>
        (Scheme.Hom.relativeDifferentials f).presheaf.map h.op
          (siteSectionSemilinearEquiv (Scheme.Hom.relativeDifferentials f) U (v i))) :=
      biderivationAlternating_natural f B hR (leOfHom h) _
    _ = biderivationAlternating f B hR V (fun i =>
        siteSectionSemilinearEquiv (Scheme.Hom.relativeDifferentials f) V
          ((SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
            (Scheme.Hom.relativeDifferentials f)).map h.op (v i))) :=
      congrArg (biderivationAlternating f B hR V)
        (funext fun i => (siteSectionSemilinearEquiv_natural (Scheme.Hom.relativeDifferentials f) h (v i)).symm)
    _ = _ := (biderivationRawAlternating_eval f B hR V _).symm

set_option backward.isDefEq.respectTransparency false in
def biderivationExteriorPresheaf :
    PresheafOfModules.extPow (O:=X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
        (Scheme.Hom.relativeDifferentials f)) ⟶
      SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X)
        (SheafOfModules.unit (structureSheaf X.sheaf)) :=
  PresheafExterior.desc (O:=X.sheaf.obj) (fun U => biderivationRawAlternating f B hR U.unop)
    (fun h v => biderivationRawAlternating_natural f B hR h.unop v)

/-- The actual alternating cotangent functional represented by a relative
structure-sheaf biderivation, with no Jacobi or smoothness assumption. -/
def biderivationExteriorMorphism :
    Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ) ⟶
      SheafOfModules.unit (structureSheaf X.sheaf) :=
  descendExteriorPresheafMorphism (Scheme.Hom.relativeDifferentials f)
    (SheafOfModules.unit (structureSheaf X.sheaf)) (biderivationExteriorPresheaf f B hR)

/-- A genuine sheaf morphism to the unit gives a genuine global dual-sheaf section. -/
def dualGlobalSectionOfHom (M : X.Modules)
    (φ : M ⟶ SheafOfModules.unit (structureSheaf X.sheaf)) : Γ(dualSheaf M,⊤) :=
  localHomOfFamily M (SheafOfModules.unit (structureSheaf X.sheaf)) ⊤
    (fun V _ a => φ.app V a)
    (fun V _ a b => (φ.app V).hom.map_add a b)
    (fun _V _ r a => φ.app_smul r a)
    (fun _V _W hVW _ a => congrArg (fun k => k a) (φ.mapPresheaf.naturality (homOfLE hVW).op))

def biderivationCotangentDualSection :
    Γ(dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)),⊤) :=
  dualGlobalSectionOfHom _ (biderivationExteriorMorphism f B hR)
end NcCubic.Geometry
