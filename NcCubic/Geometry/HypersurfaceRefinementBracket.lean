module
public import NcCubic.Geometry.HypersurfaceRefinementKernel
public import NcCubic.Geometry.BracketDescent
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ} {Z : Scheme}

section
variable (ι : Z ⟶ ProjectiveAmbient n) [IsClosedImmersion ι]
  (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
  (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
    (homogeneousSubmodule (Fin (n+1)) ℂ) ι = Ideal.span {F})
  (i : Fin (n+1)) {g : CubicPolynomial (n+1)} {e : ℕ} (hg : g.IsHomogeneous e)

abbrev refinementAmbientBracket :=
  HomogeneousSections.bracket (contractionCoefficients F P)
    (contractionCoefficients_isHomogeneous F P hF) (show 0 < 1+e by omega)
    ((isHomogeneous_X ℂ i).mul hg)

abbrev refinementApp :=
  (ι.app (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i*g))).hom

include hg in
theorem refinementApp_surjective : Function.Surjective (refinementApp ι i (g:=g)) :=
  ι.app_surjective _ (Proj.isAffineOpen_basicOpen _ _ ((isHomogeneous_X ℂ i).mul hg) (by omega))

include hideal in
theorem refinementAmbientBracket_congr {a b a' b'}
    (ha : refinementApp ι i (g:=g) a = refinementApp ι i (g:=g) a')
    (hb : refinementApp ι i (g:=g) b = refinementApp ι i (g:=g) b') :
    refinementApp ι i (g:=g) (refinementAmbientBracket F P hF i hg a b) =
      refinementApp ι i (g:=g) (refinementAmbientBracket F P hF i hg a' b') := by
  apply BracketDescent.congr_of_kernel _ _
    (HomogeneousSections.bracket_add_right _ _ _ _)
    (HomogeneousSections.bracket_skew _ _ (contraction_skew F P) _ _)
    (hypersurface_refinement_kernel_stable ι F P hF hideal i hg rfl) ha hb

/-- The actual quotient operation on sections of a homogeneous refinement of
a hypersurface standard chart. -/
def hypersurfaceRefinementBracket :=
  BracketDescent.operation (refinementApp ι i (g:=g)) (refinementApp_surjective ι i hg)
    (refinementAmbientBracket F P hF i hg)

include hideal in
theorem hypersurfaceRefinementBracket_pullback (a b) :
    hypersurfaceRefinementBracket ι F P hF i hg
      (refinementApp ι i (g:=g) a) (refinementApp ι i (g:=g) b) =
      refinementApp ι i (g:=g) (refinementAmbientBracket F P hF i hg a b) :=
  BracketDescent.operation_map _ _ _ (fun ha hb =>
    refinementAmbientBracket_congr ι F P hF hideal i hg ha hb) a b
include hideal

theorem hypersurfaceRefinementBracket_add_right (a b c) :
    hypersurfaceRefinementBracket ι F P hF i hg a (b+c) =
      hypersurfaceRefinementBracket ι F P hF i hg a b +
      hypersurfaceRefinementBracket ι F P hF i hg a c :=
  BracketDescent.operation_add_right _ _ _
    (fun ha hb => refinementAmbientBracket_congr ι F P hF hideal i hg ha hb)
    (HomogeneousSections.bracket_add_right _ _ _ _) a b c

theorem hypersurfaceRefinementBracket_skew (a b) :
    hypersurfaceRefinementBracket ι F P hF i hg a b =
      -hypersurfaceRefinementBracket ι F P hF i hg b a :=
  BracketDescent.operation_skew _ _ _
    (fun ha hb => refinementAmbientBracket_congr ι F P hF hideal i hg ha hb)
    (HomogeneousSections.bracket_skew _ _ (contraction_skew F P) _ _) a b

theorem hypersurfaceRefinementBracket_self (a) :
    hypersurfaceRefinementBracket ι F P hF i hg a a = 0 :=
  BracketDescent.operation_self _ _ _
    (fun ha hb => refinementAmbientBracket_congr ι F P hF hideal i hg ha hb)
    (HomogeneousSections.bracket_self _ _ (contraction_skew F P) _ _) a

theorem hypersurfaceRefinementBracket_leibniz (a b c) :
    hypersurfaceRefinementBracket ι F P hF i hg a (b*c) =
      b*hypersurfaceRefinementBracket ι F P hF i hg a c +
      c*hypersurfaceRefinementBracket ι F P hF i hg a b :=
  BracketDescent.operation_leibniz _ _ _
    (fun ha hb => refinementAmbientBracket_congr ι F P hF hideal i hg ha hb)
    (HomogeneousSections.bracket_leibniz _ _ _ _) a b c

theorem hypersurfaceRefinementBracket_jacobi
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P))) (a b c) :
    hypersurfaceRefinementBracket ι F P hF i hg a (hypersurfaceRefinementBracket ι F P hF i hg b c) +
    hypersurfaceRefinementBracket ι F P hF i hg b (hypersurfaceRefinementBracket ι F P hF i hg c a) +
    hypersurfaceRefinementBracket ι F P hF i hg c (hypersurfaceRefinementBracket ι F P hF i hg a b) = 0 :=
  BracketDescent.operation_jacobi _ _ _
    (fun ha hb => refinementAmbientBracket_congr ι F P hF hideal i hg ha hb)
    (HomogeneousSections.bracket_jacobi _ _ (contraction_skew F P) hJac _ _) a b c

end
end NcCubic.Geometry
