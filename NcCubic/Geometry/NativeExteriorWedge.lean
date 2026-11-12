/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorWedgeMap
public import NcCubic.Geometry.BivectorEvaluation
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
/-- The native local wedge is the ordered product of the actual exterior generators. -/
theorem exteriorWedgeAlternating_homogeneousProd {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (v : Fin 2 → Γ(M,U)) :
    exteriorWedgeAlternating M U v =
      (Scheme.Modules.exteriorAlgebra M).toPresheafGradedAlgebra.homogeneousProd (op U) 2
        (fun i => (Scheme.Modules.exteriorGenerator M).val.app (op U) (v i)) := by
  rw [exteriorWedgeAlternating_eval]
  have h := exteriorPresheafUnit_wedgeSection M (op U)
    (fun i => (siteSectionSemilinearEquiv M U).symm (v i))
  exact congrArg (siteSectionSemilinearEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) U) h

/-- Naturality of the actual local wedge under an actual sheaf morphism. -/
theorem exteriorWedgeAlternating_map {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) (v : Fin 2 → Γ(M,U)) :
    (Scheme.Modules.exteriorPowerMap f 2).val.app (op U) (exteriorWedgeAlternating M U v) =
      exteriorWedgeAlternating N U (fun i => f.val.app (op U) (v i)) := by
  rw [exteriorWedgeAlternating_homogeneousProd,exteriorWedgeAlternating_homogeneousProd]
  exact exteriorPowerMap_homogeneousProd f 2 (op U) v

/-- The native wedge of actual tangent fields has determinant bracket evaluation. -/
theorem bivectorSectionBracket_native_wedge {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (v : Fin 2 → Γ(tangentSheaf f,U)) (a b : Γ(X,U)) :
    bivectorSectionBracket f U (exteriorWedgeAlternating (tangentSheaf f) U v) a b =
      tangentSectionDerivation f U (v 0) a * tangentSectionDerivation f U (v 1) b -
      tangentSectionDerivation f U (v 1) a * tangentSectionDerivation f U (v 0) b := by
  have h := bivectorSectionBracket_wedge f U
    (fun i => (siteSectionSemilinearEquiv (tangentSheaf f) U).symm (v i)) a b
  simpa only [exteriorWedgeAlternating_eval, tangentWedgeSection, bivectorSheaf,
    LinearEquiv.apply_symm_apply] using h
end NcCubic.Geometry
