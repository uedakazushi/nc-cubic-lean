module
public import NcCubic.Geometry.SheafBiderivationExterior
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The genuine cotangent exterior wedge on an arbitrary open, defined using
the canonical exterior sheafification unit rather than an affine-only isomorphism. -/
def cotangentWedgeSection {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (v : Fin 2 → Γ(Scheme.Hom.relativeDifferentials f,U)) :
    Γ(Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ),U) :=
  siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)) U
    (exteriorUnitWedge (Scheme.Hom.relativeDifferentials f) U
      (fun i => (siteSectionSemilinearEquiv (Scheme.Hom.relativeDifferentials f) U).symm (v i)))

theorem dualGlobalSectionOfHom_eval {X : Scheme.{u}} (M : X.Modules)
    (φ : M ⟶ SheafOfModules.unit (structureSheaf X.sheaf)) (U : X.Opens) (a : Γ(M,U)) :
    dualPairing M (dualGlobalSectionOfHom M φ)
      (Over.mk (homOfLE (show U≤⊤ from le_top))) a = φ.app U a := rfl

section Relative
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (B : StructureSheafBiderivation X) (hR : B.IsRelative f)

set_option backward.isDefEq.respectTransparency false in
theorem biderivationExteriorMorphism_wedge (U : X.Opens)
    (v : Fin 2 → Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (biderivationExteriorMorphism f B hR).app U (cotangentWedgeSection f U v) =
      biderivationAlternating f B hR U v := by
  let M : X.Modules := Scheme.Hom.relativeDifferentials f
  let N : X.Modules := SheafOfModules.unit (structureSheaf X.sheaf)
  let vraw : Fin 2 → (SheafOfModules.valPresheaf (Osharp:=X.sheaf)
      (Opens.grothendieckTopology ↥X) M).obj (op U) :=
    fun i => (siteSectionSemilinearEquiv M U).symm (v i)
  let α := biderivationExteriorPresheaf f B hR
  have hp : α.app (op U) (exteriorRawWedge M U vraw) = biderivationRawAlternating f B hR U vraw :=
    PresheafExterior.desc_wedgeSection (O:=X.sheaf.obj)
      (SheafOfModules.valPresheaf (Osharp:=X.sheaf) (Opens.grothendieckTopology ↥X) M) 2
      (fun V => biderivationRawAlternating f B hR V.unop)
      (fun h w => biderivationRawAlternating_natural f B hR h.unop w) (op U) vraw
  calc
    _ = siteSectionSemilinearEquiv N U
        (((moduleUnderlyingFunctor X).map (biderivationExteriorMorphism f B hR)).app (op U)
          (exteriorUnitWedge M U vraw)) :=
      (siteSectionSemilinearEquiv_map (biderivationExteriorMorphism f B hR) U _).symm
    _ = siteSectionSemilinearEquiv N U (α.app (op U) (exteriorRawWedge M U vraw)) :=
      congrArg (siteSectionSemilinearEquiv N U) (exteriorUnitWedge_descend M N α U vraw)
    _ = siteSectionSemilinearEquiv N U (biderivationRawAlternating f B hR U vraw) :=
      congrArg (siteSectionSemilinearEquiv N U) hp
    _ = biderivationAlternating f B hR U (fun i => siteSectionSemilinearEquiv M U (vraw i)) :=
      biderivationRawAlternating_eval f B hR U vraw
    _ = _ := congrArg (biderivationAlternating f B hR U)
      (funext fun i => (siteSectionSemilinearEquiv M U).apply_symm_apply (v i))

theorem biderivationCotangentDualSection_wedge (U : X.Opens)
    (v : Fin 2 → Γ(Scheme.Hom.relativeDifferentials f,U)) :
    dualPairing (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))
      (biderivationCotangentDualSection f B hR) (Over.mk (homOfLE (show U≤⊤ from le_top)))
      (cotangentWedgeSection f U v) = biderivationAlternating f B hR U v :=
  (dualGlobalSectionOfHom_eval _ (biderivationExteriorMorphism f B hR) U _).trans
    (biderivationExteriorMorphism_wedge f B hR U v)

/-- All-open evaluation of the actual dual exterior section recovers the
original biderivation on the genuine wedge of actual relative differentials. -/
theorem biderivationCotangentDualSection_d_wedge_d (U : X.Opens) (a b : Γ(X,U)) :
    dualPairing (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))
      (biderivationCotangentDualSection f B hR) (Over.mk (homOfLE (show U≤⊤ from le_top)))
      (cotangentWedgeSection f U
        ![(Scheme.Hom.universalRelativeDerivation f).d a,(Scheme.Hom.universalRelativeDerivation f).d b]) =
      B.bracket U a b := by
  exact (dualGlobalSectionOfHom_eval _ (biderivationExteriorMorphism f B hR) U _).trans
    ((biderivationExteriorMorphism_wedge f B hR U _).trans (biderivationAlternating_d_d f B hR U a b))
end Relative
end NcCubic.Geometry
