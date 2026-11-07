/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
/- Short restriction wrapper adapted from pinned Stacks SliceDeterminant
(5ed82d14634e8d9576bb844c7bd4e3da66d450e7, Apache 2.0). -/
module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra
public import NcCubic.Geometry.ExteriorSheafDescent
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
/-- Restricting the actual exterior sheaf is the exterior sheaf on the slice site. -/
def exteriorRestrictionIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (n : ℕ) :
    (Scheme.Modules.exteriorPower M (n:ℤ)).over U ≅
      (SheafOfModules.algebras (Osharp := X.sheaf.over U)
        ((Opens.grothendieckTopology ↥X).over U)
        (show SheafOfModules (Sheaf.toRingCat ((Opens.grothendieckTopology ↥X).over U)
          (X.sheaf.over U)) from M.over U)).exteriorPower n :=
  let A := SheafOfModules.algebras (Opens.grothendieckTopology ↥X) M
  let B := SheafOfModules.algebras (Osharp := X.sheaf.over U)
    ((Opens.grothendieckTopology ↥X).over U)
    (show SheafOfModules (Sheaf.toRingCat ((Opens.grothendieckTopology ↥X).over U)
      (X.sheaf.over U)) from M.over U)
  SheafOfModules.exteriorOverIso M A.exterior A.exteriorGenerator
    A.exterior_isExteriorAlgebra U B.exterior B.exteriorGenerator B.exterior_isExteriorAlgebra (n:ℤ)
end NcCubic.Geometry
