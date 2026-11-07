module
public import NcCubic.Geometry.ExteriorSheafDescentUnit
public import NcCubic.Geometry.RawExteriorWedge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace NcCubic.Geometry
universe u

/-- For the constructed algebra package the self-comparison is the identity,
by the exterior algebra universal property. -/
theorem exteriorPowerSheafifyIso_algebras_inv {X : Scheme.{u}} (F : X.Modules) (n : ℕ) :
    (SheafOfModules.exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X)
      (SheafOfModules.algebras _ F) n).inv = 𝟙 _ := by
  let A := SheafOfModules.algebras (Opens.grothendieckTopology ↥X) F
  let hA := A.exterior_isExteriorAlgebra.isUniversal
  change (hA.desc A.exterior A.exteriorGenerator hA.1).app (n : ℤ) = _
  have hh := hA.eq_id (hA.desc_extends A.exterior A.exteriorGenerator hA.1)
  exact congrArg (fun f => f.app (n : ℤ)) hh

/-- The transported exterior unit in an arbitrary degree. -/
def exteriorPresheafUnitDegree {X : Scheme.{u}} (F : X.Modules) (n : ℕ) :
    PresheafOfModules.extPow (O := X.sheaf.obj) n
      (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F) ⟶
      SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (Scheme.Modules.exteriorPower F (n : ℤ)) :=
  (PresheafOfModules.sheafificationAdjunction
    (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X)
      (𝟙 X.sheaf.obj))).unit.app _ ≫
    (moduleUnderlyingFunctor X).map
      (SheafOfModules.exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X)
        (SheafOfModules.algebras _ F) n).inv

/-- The comparison in degree two is the unit used by bivector descent. -/
theorem exteriorPresheafUnitDegree_two {X : Scheme.{u}} (F : X.Modules) :
    exteriorPresheafUnitDegree F 2 = exteriorPresheafUnit F := rfl

/-- The canonical constructed exterior package has ordinary sheafification unit. -/
theorem exteriorPresheafUnitDegree_eq_sheafifyUnit {X : Scheme.{u}} (F : X.Modules) (n : ℕ) :
    exteriorPresheafUnitDegree F n =
      PresheafOfModules.sheafifyUnit
        (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X)
          (𝟙 X.sheaf.obj))
        (PresheafOfModules.extPow (O := X.sheaf.obj) n
          (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F)) := by
  unfold exteriorPresheafUnitDegree
  rw [exteriorPowerSheafifyIso_algebras_inv]
  let P := PresheafOfModules.extPow (O := X.sheaf.obj) n
    (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F)
  let η := (PresheafOfModules.sheafificationAdjunction
    (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X)
      (𝟙 X.sheaf.obj))).unit.app P
  have hi := (moduleUnderlyingFunctor X).map_id (Scheme.Modules.exteriorPower F (n : ℤ))
  exact (congrArg (fun k => η ≫ k) hi).trans (Category.comp_id η)

/-- The inverse counit on a sheaf section is the actual sheafification unit. -/
theorem sheafifyValIso_inv_unit {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opensᵒᵖ) (s : (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F).obj U) :
    (SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X) F).inv.val.app U s =
      PresheafOfModules.Hom.app
        (PresheafOfModules.sheafifyUnit
          (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X)
            (𝟙 X.sheaf.obj)) (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F)) U s := by
  let e := SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X) F
  have hinj : Function.Injective (e.hom.val.app U) :=
    (show Function.LeftInverse (e.inv.val.app U) (e.hom.val.app U) from
      fun t => SheafOfModules.hom_congr_app_apply e.hom_inv_id U t).injective
  apply hinj
  have hi := SheafOfModules.hom_congr_app_apply
    (SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X) F).inv_hom_id U s
  have ht := PresheafOfModules.hom_congr_apply'
    ((PresheafOfModules.sheafificationAdjunction
      (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X)
        (𝟙 X.sheaf.obj))).right_triangle_components F) U s
  exact hi.trans ht.symm

/-- The actual unit-image of a decomposable section is the ordered product
of its exterior generators, in every degree. -/
theorem exteriorPresheafUnitDegree_wedgeSection {X : Scheme.{u}} (F : X.Modules) (n : ℕ)
    (U : X.Opensᵒᵖ)
    (s : Fin n → (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F).obj U) :
    (exteriorPresheafUnitDegree F n).app U
      (PresheafExterior.wedgeSection (O := X.sheaf.obj)
        (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F) n U s) =
    (Scheme.Modules.exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd U n
      (fun i => (Scheme.Modules.exteriorGenerator F).val.app U (s i)) := by
  have hη := congrArg (fun f => PresheafOfModules.Hom.app f U
    (PresheafExterior.wedgeSection (O := X.sheaf.obj)
        (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F) n U s))
    (exteriorPresheafUnitDegree_eq_sheafifyUnit F n)
  refine hη.trans ?_
  have hu := SheafOfModules.sheafifyUnit_extPow_ιMulti
    (J := Opens.grothendieckTopology ↥X) (Osharp := X.sheaf)
    (𝟙 X.sheaf.obj) (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F) n U s
  refine hu.trans ?_
  congr 1
  funext i
  change _ = (SheafOfModules.sectionwiseExteriorAlgebraGen
    (Opens.grothendieckTopology ↥X) (𝟙 X.sheaf.obj)
      (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F)).val.app U
    ((SheafOfModules.sheafifyValIso (Opens.grothendieckTopology ↥X) F).inv.val.app U (s i))
  exact congrArg ((SheafOfModules.sectionwiseExteriorAlgebraGen
    (Opens.grothendieckTopology ↥X) (𝟙 X.sheaf.obj)
      (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F)).val.app U)
    (sheafifyValIso_inv_unit F U (s i)).symm

/-- The degree-two form used by the actual bivector/contraction dictionary. -/
theorem exteriorPresheafUnit_wedgeSection {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opensᵒᵖ)
    (s : Fin 2 → (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F).obj U) :
    (exteriorPresheafUnit F).app U
      (PresheafExterior.wedgeSection (O := X.sheaf.obj)
        (SheafOfModules.valPresheaf (Osharp := X.sheaf) (Opens.grothendieckTopology ↥X) F) 2 U s) =
    (Scheme.Modules.exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd U 2
      (fun i => (Scheme.Modules.exteriorGenerator F).val.app U (s i)) :=
  exteriorPresheafUnitDegree_wedgeSection F 2 U s

end NcCubic.Geometry
