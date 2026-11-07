/-
Actual restriction of global sections along a projective cubic hypersurface.
Vanishing of the raw H0/H1 of the negative twist gives a native linear
equivalence. Its forward map is literally the actual adjunction unit on top
sections, including the actual coefficient pullback action on source sections.
-/
module
public import NcCubic.Geometry.HypersurfaceRestrictionSequence
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedSections
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
attribute [local instance] HasDerivedCategory.standard
namespace NcCubic.Geometry.HypersurfaceRestrictionSections

lemma isIso_sections_map_of_vanishing {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact)
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived 0).obj S.X₁))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor X ⊤).rightDerived 1).obj S.X₁)) :
    IsIso ((Stacks.Cohomology.sectionsFunctor X ⊤).map S.g) := by
  let G := Stacks.Cohomology.sectionsFunctor X ⊤
  have hm := Stacks.Cohomology.SectionsEpi.shortExact_map_of_isZero_rightDerived_one G hS h1
  have hz : IsZero (G.obj S.X₁) :=
    h0.of_iso ((G.rightDerivedZeroIsoSelf).app S.X₁).symm
  exact (hm.isIso_g_iff).2 hz

abbrev restrictedPushforward {Z X : Scheme.{u}} (i : Z ⟶ X) (M : X.Modules) : X.Modules :=
  (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj M)

/-- The literal global section map of the actual restriction unit. -/
def restrictionLinearMap {Z X : Scheme.{u}} (i : Z ⟶ X) (M : X.Modules) :
    Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(restrictedPushforward i M, ⊤) :=
  ((Stacks.Cohomology.sectionsFunctor X ⊤).map
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)).hom

lemma restrictionLinearMap_apply {Z X : Scheme.{u}} (i : Z ⟶ X) (M : X.Modules)
    (s : Γ(M, ⊤)) : restrictionLinearMap i M s =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app ⊤ s := rfl

open HypersurfaceSection HypersurfaceRestrictionSequence
open Stacks.AlgebraicGeometry.ProjPolyChart
open AlgebraicGeometry.ProjectiveSpectrum.Proj
attribute [local instance] MvPolynomial.gradedAlgebra

lemma isIso_cubicRestriction_sections {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (M : (ambient n).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M)
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj (twisted n M)))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj (twisted n M))) :
    IsIso ((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)) := by
  obtain ⟨w,hSE⟩ := cubicRestriction_shortExact i F hF0 hideal M hM
  exact isIso_sections_map_of_vanishing hSE h0 h1

/-- Restriction is an equivalence under the explicit H⁰/H¹ negative-twist vanishings.
Its forward map remains the literal global sections map of the restriction unit. -/
def cubicRestrictionLinearEquiv {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (M : (ambient n).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M)
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj (twisted n M)))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj (twisted n M))) :
    Γ(M, ⊤) ≃ₗ[Γ(ambient n, ⊤)] Γ(restrictedPushforward i M, ⊤) := by
  let := isIso_cubicRestriction_sections i F hF0 hideal M hM h0 h1
  exact (asIso ((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).map
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M))).toLinearEquiv

lemma cubicRestrictionLinearEquiv_apply {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (M : (ambient n).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M)
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj (twisted n M)))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj (twisted n M)))
    (s : Γ(M, ⊤)) :
    cubicRestrictionLinearEquiv i F hF0 hideal M hM h0 h1 s = restrictionLinearMap i M s := rfl
/-- The actual action on top sections of the direct image, read on the
identical carrier of top sections over the source scheme. -/
@[instance_reducible] def pushforwardTopModule {Z X : Scheme.{u}} (i : Z ⟶ X) (N : Z.Modules) :
    Module Γ(X, ⊤) Γ(N, ⊤) :=
  inferInstanceAs (Module Γ(X, ⊤) Γ((Scheme.Modules.pushforward i).obj N, ⊤))

lemma pushforwardTopModule_smul {Z X : Scheme.{u}} (i : Z ⟶ X) (N : Z.Modules) :
    letI := pushforwardTopModule i N
    ∀ (c : Γ(X, ⊤)) (s : Γ(N, ⊤)), c • s = (i.appTop.hom c) • s := by
  intro c s
  rfl

/-- Native sections on the hypersurface itself, with the actual coefficient
pullback action, are obtained by the literal restriction-unit map. -/
def cubicRestrictionSectionsEquiv {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (M : (ambient n).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M)
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj (twisted n M)))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj (twisted n M))) :
    letI := pushforwardTopModule i ((Scheme.Modules.pullback i).obj M)
    Γ(M, ⊤) ≃ₗ[Γ(ambient n, ⊤)] Γ((Scheme.Modules.pullback i).obj M, ⊤) :=
  cubicRestrictionLinearEquiv i F hF0 hideal M hM h0 h1

lemma cubicRestrictionSectionsEquiv_apply {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (M : (ambient n).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M)
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj (twisted n M)))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj (twisted n M)))
    (s : Γ(M, ⊤)) :
    cubicRestrictionSectionsEquiv i F hF0 hideal M hM h0 h1 s =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app ⊤ s := rfl

/-- Every actual section on the hypersurface has a unique ambient lift, and
the lifting equation is the literal component of the restriction unit. -/
lemma existsUnique_cubicRestriction_lift {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (M : (ambient n).Modules) (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M)
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj (twisted n M)))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj (twisted n M)))
    (s : Γ((Scheme.Modules.pullback i).obj M, ⊤)) :
    ∃! t : Γ(M, ⊤), ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app ⊤ t = s := by
  exact (cubicRestrictionSectionsEquiv i F hF0 hideal M hM h0 h1).bijective.existsUnique s

end NcCubic.Geometry.HypersurfaceRestrictionSections
