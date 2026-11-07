module
public import NcCubic.Geometry.ProjectiveHypersurfacePoisson
public import NcCubic.Geometry.ProjectiveSectionBracket
public import NcCubic.Geometry.ChartJacobiDivisibility
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceChart
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

def projectiveHypersurfaceChartSectionsEquiv
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1)) :
    ProjectiveHypersurfaceChartRing F hF i ≃+* Γ(Z,Stacks.ProjectiveChart.subschemeChart ι i) := by
  let e := Stacks.ProjectiveChart.chartRingEquiv ℂ i
  have hEq : Ideal.span ({projectiveEquation F hF i} : Set (ProjectiveChartRing i)) =
      (Ideal.span {Stacks.ProjectiveChart.dehomCoeff ℂ i F}).map e.toRingHom := by
    rw [Ideal.map_span,Set.image_singleton]
    congr 2
    exact (Stacks.ProjectiveChart.chartRingEquiv_dehomCoeff ℂ i 3 F hF).symm
  exact (Ideal.quotientEquiv _ _ e hEq).symm.trans
    (Stacks.ProjectiveChart.chartQuotientEquiv (d:=3) ι i F hF hideal)

theorem projectiveHypersurfaceChartSectionsEquiv_mk
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1))
    (x : ProjectiveChartRing i) :
    projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i (Ideal.Quotient.mk _ x) =
      (ι.app (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))).hom
        (homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos x) := by
  change Stacks.ProjectiveChart.chartPresentation ι i
    ((Stacks.ProjectiveChart.chartRingEquiv ℂ i).symm x) = _
  change (ι.app _).hom
    ((homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos)
      ((Stacks.ProjectiveChart.chartRingEquiv ℂ i)
        ((Stacks.ProjectiveChart.chartRingEquiv ℂ i).symm x))) = _
  rw [RingEquiv.apply_symm_apply]


/-- The computed hypersurface bracket as an operation on genuine structure-sheaf sections. -/
def hypersurfaceSectionBracket
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1))
    (a b : Γ(Z,Stacks.ProjectiveChart.subschemeChart ι i)) :=
  let e := projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i
  e (projectiveHypersurfaceBracket F P hF i (e.symm a) (e.symm b))

@[simp] theorem hypersurfaceSectionBracket_equiv
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1))
    (a b : ProjectiveHypersurfaceChartRing F hF i) :
    hypersurfaceSectionBracket ι F P hF hideal i
      (projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i a)
      (projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i b) =
    projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i
      (projectiveHypersurfaceBracket F P hF i a b) := by
  simp only [hypersurfaceSectionBracket,RingEquiv.symm_apply_apply]

/-- The quotient bracket commutes with the actual pullback of ambient sections. -/
theorem hypersurfaceSectionBracket_pullback
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) (i : Fin (n+1))
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i))) :
    hypersurfaceSectionBracket ι F P hF hideal i ((ι.app _).hom a) ((ι.app _).hom b) =
      (ι.app _).hom (projectiveSectionBracket F P hF i a b) := by
  let e := homogeneousSectionsEquiv (isHomogeneous_X ℂ i) Nat.one_pos
  obtain ⟨x,rfl⟩ := e.surjective a
  obtain ⟨y,rfl⟩ := e.surjective b
  rw [← projectiveHypersurfaceChartSectionsEquiv_mk ι F hF hideal i x,
    ← projectiveHypersurfaceChartSectionsEquiv_mk ι F hF hideal i y,
    hypersurfaceSectionBracket_equiv,projectiveHypersurfaceBracket_mk,
    projectiveHypersurfaceChartSectionsEquiv_mk]
  congr 1
  exact (projectiveSectionBracket_equiv F P hF i x y).symm

/-- Jacobi on the genuine standard-chart section operations lifts to the full
homogeneous polynomial Jacobi identity. -/
theorem polynomialJacobi_of_hypersurfaceSectionJacobi
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (hN : 5 ≤ n+1) (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0)
    (P : Trivector (n+1)) (hF : F.IsHomogeneous 3) (hgrad : HasIsolatedGradientZero F)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hJac : ∀ i (a b c : Γ(Z,Stacks.ProjectiveChart.subschemeChart ι i)),
      hypersurfaceSectionBracket ι F P hF hideal i a
        (hypersurfaceSectionBracket ι F P hF hideal i b c) +
      hypersurfaceSectionBracket ι F P hF hideal i b
        (hypersurfaceSectionBracket ι F P hF hideal i c a) +
      hypersurfaceSectionBracket ι F P hF hideal i c
        (hypersurfaceSectionBracket ι F P hF hideal i a b) = 0) :
    SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)) := by
  apply polynomialJacobi_of_hypersurfaceChartJacobi hN F hF0 hF hgrad P
  intro i a b c
  let e := projectiveHypersurfaceChartSectionsEquiv ι F hF hideal i
  apply e.injective
  have hh := hJac i (e a) (e b) (e c)
  simp only [e,hypersurfaceSectionBracket_equiv] at hh
  simpa only [map_add,map_zero,e] using hh
end NcCubic.Geometry
