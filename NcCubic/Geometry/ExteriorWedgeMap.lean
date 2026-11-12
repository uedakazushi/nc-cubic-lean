/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorUnitGenerators
public import NcCubic.Geometry.ExteriorWedgeLaws
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
/-- The actual exterior map carries the ordered product of generators to the
ordered product of their actual images, in every degree. -/
theorem exteriorPowerMap_homogeneousProd {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) (U : X.Opensᵒᵖ) (s : Fin n → M.val.obj U) :
    (Scheme.Modules.exteriorPowerMap f (n:ℤ)).val.app U
      ((Scheme.Modules.exteriorAlgebra M).toPresheafGradedAlgebra.homogeneousProd U n
        (fun i => (Scheme.Modules.exteriorGenerator M).val.app U (s i))) =
      (Scheme.Modules.exteriorAlgebra N).toPresheafGradedAlgebra.homogeneousProd U n
        (fun i => (Scheme.Modules.exteriorGenerator N).val.app U (f.val.app U (s i))) := by
  let hM := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra M
  let hN := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra N
  have hgen := hM.map_app_one hN f
  exact (SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd (hM.map hN f) U n
    (fun i => (Scheme.Modules.exteriorGenerator M).val.app U (s i))).trans
      (congrArg ((Scheme.Modules.exteriorAlgebra N).toPresheafGradedAlgebra.homogeneousProd U n)
        (funext fun i => SheafOfModules.hom_congr_app_apply hgen U (s i)))
end NcCubic.Geometry
