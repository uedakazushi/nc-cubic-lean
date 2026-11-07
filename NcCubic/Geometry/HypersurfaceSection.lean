/- The actual cubic section of O(3) on projective space.
A nonzero homogeneous polynomial gives a nonzero section; its actual zero-scheme
ideal sheaf equals the defining ideal sheaf of the given closed immersion.
The elementary top-section construction follows pinned Stacks
Algebra/Homology/StrictlyPerfectRestriction. -/
module
public import NcCubic.Geometry.CanonicalHypersurface
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.IdealSheafOfHypersurface
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart
open AlgebraicGeometry.ProjectiveSpectrum.Proj
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules Scheme.Modules.Hom
attribute [local instance_reducible] ProjectiveSpectrum.top
universe u
namespace NcCubic.Geometry.HypersurfaceSection
abbrev ambient (n : ℕ) := AlgebraicGeometry.Proj (polyGrading ℂ n)
abbrev twist (n : ℕ) (d : ℤ) : (ambient n).Modules :=
  twistingSheafModule (polyGrading ℂ n) d
/-- Restrict an actual top section to every open (pinned Stacks construction). -/
def presheafSectionOfTop {T : TopCat.{u}} {R : (TopologicalSpace.Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (M : _root_.PresheafOfModules.{u} R) (m : M.obj (op ⊤)) : M.sections :=
  M.sectionsMk (fun V => M.map (homOfLE le_top : V.unop ⟶ ⊤).op m) (fun {V W} f => by
    rw [← M.map_comp_apply]
    exact M.congr_map_apply (Subsingleton.elim _ _) m)

lemma presheafSectionOfTop_eval_top {T : TopCat.{u}}
    {R : (TopologicalSpace.Opens T)ᵒᵖ ⥤ RingCat.{u}}
    (M : _root_.PresheafOfModules.{u} R) (m : M.obj (op ⊤)) :
    (presheafSectionOfTop M m).eval (op ⊤) = m := by
  change M.map (homOfLE le_top : (⊤ : TopologicalSpace.Opens T) ⟶ ⊤).op m = m
  rw [M.congr_map_apply (Subsingleton.elim _ (𝟙 (op (⊤ : TopologicalSpace.Opens T)))) m]
  simp
  rfl

def sectionOfTop {X : Scheme.{u}} (M : X.Modules) (m : Γ(M, ⊤)) : M.sections :=
  presheafSectionOfTop M.val m

lemma sectionOfTop_eval_top {X : Scheme.{u}} (M : X.Modules) (m : Γ(M, ⊤)) :
    (sectionOfTop M m).eval (op ⊤) = m :=
  presheafSectionOfTop_eval_top M.val m

def cubicSection {n : ℕ} (F : polyGrading ℂ n 3) : (twist n 3).sections :=
  sectionOfTop _ (degreeSection (polyGrading ℂ n) 3 F)

lemma degreeSection_ne_zero {n : ℕ} (F : polyGrading ℂ n 3)
    (hF : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0) :
    degreeSection (polyGrading ℂ n) 3 F ≠ 0 := by
  intro h
  obtain ⟨m,hm⟩ := exists_pow_mul_eq_zero_of_degreeSection_eq_zero (polyGrading ℂ n) F h
    (X_mem_one ℂ n 0)
  rcases mul_eq_zero.1 hm with hx | hx
  · exact pow_ne_zero m (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (n+1))) hx
  · exact hF hx


instance twist_isInvertible (n : ℕ) (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (ambient n).sheaf.obj
      (ambient n).ringCatSheaf.property (twist n d) :=
  algebraicGeometry_isInvertible_twistingSheaf (polyGrading ℂ n)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) ℂ) d

lemma cubicSection_eval_ne_zero {n : ℕ} (F : polyGrading ℂ n 3)
    (hF : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0) :
    (cubicSection F).eval (op ⊤) ≠ 0 := by
  have ht := sectionOfTop_eval_top (twist n 3) (degreeSection (polyGrading ℂ n) 3 F)
  exact fun h => degreeSection_ne_zero F hF (ht.symm.trans h)

lemma ker_eq_zeroScheme {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i] (F : polyGrading ℂ n 3)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)}) :
    i.ker = zeroScheme (ambient n) (twist n 3) ((cubicSection F).eval (op ⊤)) := by
  have ht := sectionOfTop_eval_top (twist n 3) (degreeSection (polyGrading ℂ n) 3 F)
  exact (projectiveSpace_ker_eq_zeroScheme_of_idealOfClosedSubscheme_eq_span ℂ (n+1) i F hideal).trans
    (congrArg (fun s : Γ(twist n 3, ⊤) => zeroScheme (ambient n) (twist n 3) s) ht).symm
end NcCubic.Geometry.HypersurfaceSection
