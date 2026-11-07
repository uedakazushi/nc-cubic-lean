/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.BivectorSheafDesc
@[expose] public noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem contractionSectionBracket_wedge (U : X.Opens)
    (v : Fin 2 → Γ(tangentSheaf f,U)) (a b : Γ(X,U)) :
    contractionSectionBracket f U (wedgeContractionLocal f U v) a b =
      tangentSectionDerivation f U (v 0) a * tangentSectionDerivation f U (v 1) b -
      tangentSectionDerivation f U (v 1) a * tangentSectionDerivation f U (v 0) b := by
  have hw := wedgeContractionLocal_app f U v (op (Over.mk (𝟙 U)))
    ((Scheme.Hom.universalRelativeDerivation f).d a)
  have hr (t : Γ(tangentSheaf f,U)) :
      (tangentSheaf f).presheaf.map (Over.mk (𝟙 U)).hom.op t = t := by
    change (tangentSheaf f).presheaf.map (𝟙 (op U)) t = t
    rw [CategoryTheory.Functor.map_id]
    rfl
  simp only [hr] at hw
  have hh : contractionHamiltonian f U (wedgeContractionLocal f U v) a =
      tangentSectionDerivation f U (v 0) a • v 1 -
      tangentSectionDerivation f U (v 1) a • v 0 := by
    exact hw
  change tangentEvaluation f U (contractionHamiltonian f U (wedgeContractionLocal f U v) a)
    ((Scheme.Hom.universalRelativeDerivation f).d b) = _
  rw [hh]
  change tangentEvaluationLinear f U _ _ = _
  rw [map_sub,map_smul,map_smul]
  rfl

end NcCubic.Geometry
