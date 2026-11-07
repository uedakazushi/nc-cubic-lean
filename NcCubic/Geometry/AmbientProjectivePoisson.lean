/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.HomogeneousSectionBracket
public import NcCubic.Geometry.BasisPoissonGluing
public import StacksFrontier.AlgebraicGeometry.ProjShared.RelevantCover
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace NcCubic.Geometry
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 600000
variable {n : ℕ}

/-- The genuine positive homogeneous projective basic opens, with their
positive degree and homogeneous polynomial both explicit. -/
abbrev PositiveBasicIndex (n : ℕ) :=
  Σ d : ℕ+, homogeneousSubmodule (Fin (n+1)) ℂ (d : ℕ)

def positiveBasicOpen (s : PositiveBasicIndex n) : (ProjectiveAmbient n).Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (s.2 : CubicPolynomial (n+1))

theorem positiveBasicOpen_cover (U : (ProjectiveAmbient n).Opens) :
    U ≤ ⨆ s : {s : PositiveBasicIndex n // positiveBasicOpen s ≤ U}, positiveBasicOpen s.val := by
  intro x hx
  obtain ⟨d,f,hd,hf,hxf,hfU⟩ :=
    Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le
      (homogeneousSubmodule (Fin (n+1)) ℂ) hx
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨⟨⟨d,hd⟩,⟨f,hf⟩⟩,hfU⟩,hxf⟩

private theorem ambient_res_comp {X : Scheme} {U V T : X.Opens}
    (h : T ≤ V) (k : V ≤ U) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE k).op) a) =
      (X.presheaf.map (homOfLE (h.trans k)).op) a := by
  rw [← ConcreteCategory.comp_apply,← X.presheaf.map_comp]
  rfl

/-- The actual homogeneous-basis bracket data induced by the polynomial
coefficient bivector, with no Jacobi assumption. -/
def ambientBasisBracket
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) :
    BasisBracketData (ProjectiveAmbient n) positiveBasicOpen where
  cover := positiveBasicOpen_cover
  bracket s := HomogeneousSections.bracket q hq s.1.pos s.2.property
  overlap i j a b c d ha hb := by
    let X := ProjectiveAmbient n
    let V := positiveBasicOpen i ⊓ positiveBasicOpen j
    let T := Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ)
      ((i.2 : CubicPolynomial (n+1))*j.2)
    have hTV : T ≤ V := by
      simpa only [T,V,positiveBasicOpen] using
        (Proj.basicOpen_mul (homogeneousSubmodule (Fin (n+1)) ℂ)
          (i.2 : CubicPolynomial (n+1)) j.2).le
    have hVT : V ≤ T := by
      simpa only [T,V,positiveBasicOpen] using
        (Proj.basicOpen_mul (homogeneousSubmodule (Fin (n+1)) ℂ)
          (i.2 : CubicPolynomial (n+1)) j.2).ge
    have ha0 := congrArg (fun z => (X.presheaf.map (homOfLE hTV).op) z) ha
    have hb0 := congrArg (fun z => (X.presheaf.map (homOfLE hTV).op) z) hb
    have ha' : projectiveSectionRestriction
        (show (i.2 : CubicPolynomial (n+1)) ∣ (i.2 : CubicPolynomial (n+1))*j.2 from ⟨j.2,rfl⟩) a =
      projectiveSectionRestriction
        (show (j.2 : CubicPolynomial (n+1)) ∣ (i.2 : CubicPolynomial (n+1))*j.2 from
          ⟨i.2,mul_comm (i.2 : CubicPolynomial (n+1)) j.2⟩) c := ha0
    have hb' : projectiveSectionRestriction
        (show (i.2 : CubicPolynomial (n+1)) ∣ (i.2 : CubicPolynomial (n+1))*j.2 from ⟨j.2,rfl⟩) b =
      projectiveSectionRestriction
        (show (j.2 : CubicPolynomial (n+1)) ∣ (i.2 : CubicPolynomial (n+1))*j.2 from
          ⟨i.2,mul_comm (i.2 : CubicPolynomial (n+1)) j.2⟩) d := hb0
    have h := HomogeneousSections.bracket_overlap q hq i.1.pos i.2.property j.1.pos j.2.property
      a b c d ha' hb'
    have hprod : (X.presheaf.map (homOfLE hTV).op)
        ((X.presheaf.map (homOfLE inf_le_left).op)
          (HomogeneousSections.bracket q hq i.1.pos i.2.property a b)) =
      (X.presheaf.map (homOfLE hTV).op)
        ((X.presheaf.map (homOfLE inf_le_right).op)
          (HomogeneousSections.bracket q hq j.1.pos j.2.property c d)) := by
      exact h
    have hh := congrArg (fun z => (X.presheaf.map (homOfLE hVT).op) z) hprod
    simpa [ambient_res_comp] using hh
/-- Homogeneous quadratic polynomial Poisson arrays give genuine Poisson
data on the positive homogeneous basic-open basis. -/
def ambientBasisPoisson
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j)
    (hJac : SatisfiesJacobi (bracketFromCoefficients q)) :
    BasisPoissonData (ProjectiveAmbient n) positiveBasicOpen where
  toBasisBracketData := ambientBasisBracket q hq
  add_right s := HomogeneousSections.bracket_add_right q hq s.1.pos s.2.property
  skew s := HomogeneousSections.bracket_skew q hq hskew s.1.pos s.2.property
  self_eq_zero s := HomogeneousSections.bracket_self q hq hskew s.1.pos s.2.property
  leibniz s := HomogeneousSections.bracket_leibniz q hq s.1.pos s.2.property
  jacobi s := HomogeneousSections.bracket_jacobi q hq hskew hJac s.1.pos s.2.property

/-- The canonical every-open projectivization of an arbitrary homogeneous
quadratic coefficient bivector. -/
def ambientProjectiveBracket
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) : StructureSheafBracket (ProjectiveAmbient n) :=
  (ambientBasisBracket q hq).glued

/-- The genuine global Poisson operation on the full projective structure
sheaf, constructed by unique sheaf gluing of the actual homogeneous basic opens. -/
def ambientProjectivePoisson
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j)
    (hJac : SatisfiesJacobi (bracketFromCoefficients q)) : StructureSheafPoisson (ProjectiveAmbient n) :=
  (ambientBasisPoisson q hq hskew hJac).glued

/-- The global operation has the original contraction formula on each
positive homogeneous basic-open chart. -/
theorem ambientProjectivePoisson_restrict
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j)
    (hJac : SatisfiesJacobi (bracketFromCoefficients q))
    (U : (ProjectiveAmbient n).Opens) (a b : Γ(ProjectiveAmbient n,U))
    (s : PositiveBasicIndex n) (hs : positiveBasicOpen s ≤ U) :
    ((ProjectiveAmbient n).presheaf.map (homOfLE hs).op)
      ((ambientProjectivePoisson q hq hskew hJac).bracket U a b) =
    HomogeneousSections.bracket q hq s.1.pos s.2.property
      (((ProjectiveAmbient n).presheaf.map (homOfLE hs).op) a)
      (((ProjectiveAmbient n).presheaf.map (homOfLE hs).op) b) :=
  (ambientBasisPoisson q hq hskew hJac).glued_restrict U a b s hs
/-- The actual global projectivized contraction bracket of the original
cubic potential and scalar trivector, without any representation oracle. -/
def contractionProjectiveBracket
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3) :
    StructureSheafBracket (ProjectiveAmbient n) :=
  ambientProjectiveBracket (contractionCoefficients F P)
    (contractionCoefficients_isHomogeneous F P hF)

/-- Polynomial Jacobi produces an actual Poisson operation on the full
projective structure sheaf for the original contraction coefficients. -/
def contractionProjectivePoisson
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P))) :
    StructureSheafPoisson (ProjectiveAmbient n) :=
  ambientProjectivePoisson (contractionCoefficients F P)
    (contractionCoefficients_isHomogeneous F P hF) (contraction_skew F P) hJac

end NcCubic.Geometry
