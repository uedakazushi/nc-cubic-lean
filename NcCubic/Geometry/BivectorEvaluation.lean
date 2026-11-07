/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.BivectorLocalDescent
public import NcCubic.Geometry.BivectorWedgeBracket
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
/-- Evaluate an actual local tangent bivector on two actual local functions. -/
def bivectorSectionBracket (U : X.Opens) (π : Γ(bivectorSheaf f,U))
    (a b : Γ(X,U)) : Γ(X,U) :=
  contractionSectionBracket f U ((bivectorContraction f).val.app (op U) π) a b

/-- The actual exterior contraction has the usual determinant evaluation on wedges. -/
theorem bivectorSectionBracket_wedge (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Osharp := X.sheaf)
      (Opens.grothendieckTopology ↥X) (tangentSheaf f)).obj (op U)) (a b : Γ(X,U)) :
    bivectorSectionBracket f U (tangentWedgeSection f U v) a b =
      tangentSectionDerivation f U (siteSectionSemilinearEquiv (tangentSheaf f) U (v 0)) a *
        tangentSectionDerivation f U (siteSectionSemilinearEquiv (tangentSheaf f) U (v 1)) b -
      tangentSectionDerivation f U (siteSectionSemilinearEquiv (tangentSheaf f) U (v 1)) a *
        tangentSectionDerivation f U (siteSectionSemilinearEquiv (tangentSheaf f) U (v 0)) b := by
  exact (congrArg (fun c : Γ(tangentContractionSheaf f,U) => contractionSectionBracket f U c a b)
    (bivectorContraction_tangentWedgeSection f U v)).trans
    (contractionSectionBracket_wedge f U _ a b)

/-- The all-open operation of a global bivector is the evaluation of its genuine restriction. -/
theorem algebraicBivectorBracket_eq_sectionBracket (π : AlgebraicBivector f)
    (U : X.Opens) (a b : Γ(X,U)) :
    (algebraicBivectorBracket f π).bracket U a b =
      bivectorSectionBracket f U ((bivectorSheaf f).val.map (homOfLE le_top).op π) a b := by
  exact congrArg (fun c : Γ(tangentContractionSheaf f,U) => contractionSectionBracket f U c a b)
    (PresheafOfModules.naturality_apply (bivectorContraction f).val (homOfLE le_top).op π).symm
end NcCubic.Geometry
