module
public import NcCubic.Geometry.BivectorContraction
public import NcCubic.Geometry.TangentNaturality
public import NcCubic.Geometry.PoissonSheaf
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)
def contractionEvaluation (U : X.Opens) (c : Γ(tangentContractionSheaf f,U)) :
    Γ(Scheme.Hom.relativeDifferentials f,U) →ₗ[Γ(X,U)] Γ(tangentSheaf f,U) :=
  (c.app (op (Over.mk (𝟙 U)))).hom

theorem contractionEvaluation_natural {U V : X.Opens} (h : V ≤ U)
    (c : Γ(tangentContractionSheaf f,U)) (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (tangentSheaf f).val.map (homOfLE h).op (contractionEvaluation f U c a) =
    contractionEvaluation f V ((tangentContractionSheaf f).val.map (homOfLE h).op c)
      ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE h).op a) := by
  change (tangentSheaf f).val.map (homOfLE h).op ((c.app (op (Over.mk (𝟙 U)))).hom a) =
    (c.app (op (Over.mk (homOfLE h)))).hom
      ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE h).op a)
  let g : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) := Over.homMk (homOfLE h)
  exact congrArg (fun k => k.hom a) (c.naturality g.op).symm

def contractionHamiltonian (U : X.Opens) (c : Γ(tangentContractionSheaf f,U))
    (a : Γ(X,U)) : Γ(tangentSheaf f,U) :=
  contractionEvaluation f U c ((Scheme.Hom.universalRelativeDerivation f).d a)

theorem contractionHamiltonian_natural {U V : X.Opens} (h : V ≤ U)
    (c : Γ(tangentContractionSheaf f,U)) (a : Γ(X,U)) :
    (tangentSheaf f).val.map (homOfLE h).op (contractionHamiltonian f U c a) =
    contractionHamiltonian f V ((tangentContractionSheaf f).val.map (homOfLE h).op c)
      (X.presheaf.map (homOfLE h).op a) := by
  exact (contractionEvaluation_natural f h c _).trans
    (congrArg (contractionEvaluation f V ((tangentContractionSheaf f).val.map (homOfLE h).op c))
      ((Scheme.Hom.universalRelativeDerivation f).d_map (homOfLE h).op a).symm)

/-- The local operation associated with an actual cotangent-to-tangent sheaf map. -/
def contractionSectionBracket (U : X.Opens) (c : Γ(tangentContractionSheaf f,U))
    (a b : Γ(X,U)) : Γ(X,U) :=
  tangentSectionDerivation f U (contractionHamiltonian f U c a) b

theorem contractionSectionBracket_natural {U V : X.Opens} (h : V ≤ U)
    (c : Γ(tangentContractionSheaf f,U)) (a b : Γ(X,U)) :
    X.presheaf.map (homOfLE h).op (contractionSectionBracket f U c a b) =
    contractionSectionBracket f V ((tangentContractionSheaf f).val.map (homOfLE h).op c)
      (X.presheaf.map (homOfLE h).op a) (X.presheaf.map (homOfLE h).op b) := by
  exact (tangentSectionDerivation_natural f h _ b).trans
    (congrArg (fun t => tangentSectionDerivation f V t (X.presheaf.map (homOfLE h).op b))
      (contractionHamiltonian_natural f h c a))
/-- A global actual cotangent-to-tangent sheaf map defines a restriction-compatible operation. -/
def contractionGlobalBracket (c : Γ(tangentContractionSheaf f,⊤)) :
    StructureSheafBracket X where
  bracket U a b := contractionSectionBracket f U
    ((tangentContractionSheaf f).val.map (homOfLE le_top).op c) a b
  restrict {U V} h a b := by
    have hc : (tangentContractionSheaf f).val.map (homOfLE h).op
        ((tangentContractionSheaf f).val.map (homOfLE (le_top : U ≤ ⊤)).op c) =
        (tangentContractionSheaf f).val.map (homOfLE (le_top : V ≤ ⊤)).op c :=
      ((tangentContractionSheaf f).val.map_comp_apply
        (homOfLE (le_top : U ≤ ⊤)).op (homOfLE h).op c).symm
    exact (contractionSectionBracket_natural f h _ a b).trans
      (congrArg (fun d => contractionSectionBracket f V d
        (X.presheaf.map (homOfLE h).op a) (X.presheaf.map (homOfLE h).op b)) hc)

end NcCubic.Geometry
