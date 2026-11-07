module
public import NcCubic.Geometry.HypersurfaceRefinementNaturality
public import NcCubic.Geometry.HypersurfaceBasis
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 800000
variable {n : ℕ} {Z : Scheme}
private theorem hypersurface_res_comp {X : Scheme} {U V T : X.Opens}
    (h : T ≤ V) (k : V ≤ U) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE k).op) a) =
      (X.presheaf.map (homOfLE (h.trans k)).op) a := by
  rw [← ConcreteCategory.comp_apply,← X.presheaf.map_comp]
  rfl

def hypersurfaceBasisBracket
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) :
    BasisBracketData Z (subschemeRefinementOpen ι) where
  cover := subschemeRefinementOpen_cover ι
  bracket s := hypersurfaceRefinementBracket ι F P hF s.1 s.2.2.property
  overlap s t a b c d ha hb := by
    let u : ProjectiveRefinementIndex n := ⟨s.1,s.2.1+(1+t.2.1),
      (s.2.2 : CubicPolynomial (n+1)) * ((X t.1 : CubicPolynomial (n+1))*t.2.2),
      s.2.2.property.mul ((isHomogeneous_X ℂ t.1).mul t.2.2.property)⟩
    have hu : projectiveRefinementOpen u = projectiveRefinementOpen s ⊓ projectiveRefinementOpen t := by
      simp only [projectiveRefinementOpen,u,← mul_assoc,Proj.basicOpen_mul,inf_assoc]
    have hleft : projectiveRefinementOpen u ≤ projectiveRefinementOpen s := hu.le.trans inf_le_left
    have hright : projectiveRefinementOpen u ≤ projectiveRefinementOpen t := hu.le.trans inf_le_right
    let V := subschemeRefinementOpen ι s ⊓ subschemeRefinementOpen ι t
    let T := subschemeRefinementOpen ι u
    have hTV : T ≤ V := fun _ hx => ⟨hleft hx,hright hx⟩
    have hVT : V ≤ T := fun _ hx => hu.ge hx
    have ha0 := congrArg (fun z => (Z.presheaf.map (homOfLE hTV).op) z) ha
    have hb0 := congrArg (fun z => (Z.presheaf.map (homOfLE hTV).op) z) hb
    simp only [hypersurface_res_comp] at ha0 hb0
    have h1 := hypersurfaceRefinementBracket_restrict ι F P hF hideal s.1 u.1
      s.2.2.property u.2.2.property hleft a b
    have h2 := hypersurfaceRefinementBracket_restrict ι F P hF hideal t.1 u.1
      t.2.2.property u.2.2.property hright c d
    have hprod : (Z.presheaf.map (homOfLE hTV).op)
        ((Z.presheaf.map (homOfLE inf_le_left).op)
          (hypersurfaceRefinementBracket ι F P hF s.1 s.2.2.property a b)) =
      (Z.presheaf.map (homOfLE hTV).op)
        ((Z.presheaf.map (homOfLE inf_le_right).op)
          (hypersurfaceRefinementBracket ι F P hF t.1 t.2.2.property c d)) := by
      exact (hypersurface_res_comp hTV inf_le_left _).trans
        ((h1.trans ((congrArg₂ (hypersurfaceRefinementBracket ι F P hF u.1 u.2.2.property)
          ha0 hb0).trans h2.symm)).trans (hypersurface_res_comp hTV inf_le_right _).symm)
    have hh := congrArg (fun z => (Z.presheaf.map (homOfLE hVT).op) z) hprod
    simpa [hypersurface_res_comp] using hh

/-- The contraction operation on the genuine structure sheaf of the hypersurface. -/
def hypersurfaceGlobalBracket
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F}) : StructureSheafBracket Z :=
  (hypersurfaceBasisBracket ι F P hF hideal).glued

def hypersurfaceBasisPoisson
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P))) :
    BasisPoissonData Z (subschemeRefinementOpen ι) where
  toBasisBracketData := hypersurfaceBasisBracket ι F P hF hideal
  add_right s := hypersurfaceRefinementBracket_add_right ι F P hF hideal s.1 s.2.2.property
  skew s := hypersurfaceRefinementBracket_skew ι F P hF hideal s.1 s.2.2.property
  self_eq_zero s := hypersurfaceRefinementBracket_self ι F P hF hideal s.1 s.2.2.property
  leibniz s := hypersurfaceRefinementBracket_leibniz ι F P hF hideal s.1 s.2.2.property
  jacobi s := hypersurfaceRefinementBracket_jacobi ι F P hF hideal s.1 s.2.2.property hJac

/-- Actual polynomial Jacobi descends to a Poisson operation on every open of
the actual projective hypersurface, with genuine restriction compatibility. -/
def hypersurfaceGlobalPoisson
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P))) :
    StructureSheafPoisson Z :=
  (hypersurfaceBasisPoisson ι F P hF hideal hJac).glued

theorem hypersurfaceGlobalPoisson_restrict
    (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P)))
    (U : Z.Opens) (a b : Γ(Z,U)) (s : ProjectiveRefinementIndex n)
    (hs : subschemeRefinementOpen ι s ≤ U) :
    (Z.presheaf.map (homOfLE hs).op) ((hypersurfaceGlobalPoisson ι F P hF hideal hJac).bracket U a b) =
    hypersurfaceRefinementBracket ι F P hF s.1 s.2.2.property
      ((Z.presheaf.map (homOfLE hs).op) a) ((Z.presheaf.map (homOfLE hs).op) b) :=
  (hypersurfaceBasisPoisson ι F P hF hideal hJac).glued_restrict U a b s hs
end NcCubic.Geometry
