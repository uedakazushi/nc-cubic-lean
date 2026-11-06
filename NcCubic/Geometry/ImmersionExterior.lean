/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
The exterior-pullback comparison is the pinned StacksFrontier construction,
read as in AlgebraicGeometry/DeRham/ExteriorPowerPullback.lean (Apache-2.0).
-/
module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace NcCubic.Geometry.ImmersionBivector

/-- Canonical exterior pullback comparison, read directly from the exterior
algebra universal property of the cached upstream construction. -/
def exteriorPullbackIso {X P : Scheme.{u}} (i : X ⟶ P) (M : P.Modules) (n : ℤ) :
    (Scheme.Modules.pullback i).obj (Scheme.Modules.exteriorPower M n) ≅
      Scheme.Modules.exteriorPower ((Scheme.Modules.pullback i).obj M) n :=
  (Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso i.toLRSHom.toShHom
    (Scheme.Modules.exteriorAlgebra M) (Scheme.Modules.exteriorGenerator M)
    (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback i).obj M))
    (Scheme.Modules.exteriorGenerator ((Scheme.Modules.pullback i).obj M))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra M)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)).app n

def exteriorAlongPullback {X P : Scheme.{u}} (i : X ⟶ P)
    {E : X.Modules} {M : P.Modules}
    (τ : E ⟶ (Scheme.Modules.pullback i).obj M) (n : ℤ) :
    Scheme.Modules.exteriorPower E n ⟶
      (Scheme.Modules.pullback i).obj (Scheme.Modules.exteriorPower M n) :=
  Scheme.Modules.exteriorPowerMap τ n ≫ (exteriorPullbackIso i M n).inv

theorem exteriorAlongPullback_comp_comparison {X P : Scheme.{u}} (i : X ⟶ P)
    {E : X.Modules} {M : P.Modules}
    (τ : E ⟶ (Scheme.Modules.pullback i).obj M) (n : ℤ) :
    exteriorAlongPullback i τ n ≫ (exteriorPullbackIso i M n).hom =
      Scheme.Modules.exteriorPowerMap τ n := by
  simp [exteriorAlongPullback, Category.assoc]

end NcCubic.Geometry.ImmersionBivector
