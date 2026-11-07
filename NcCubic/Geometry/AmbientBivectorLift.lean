/-
Actual ambient lifts of genuine hypersurface tangent bivectors.
All maps use the genuine exterior differential and restriction adjunction unit.
The lift is coefficient-linear, unique, and faithful for genuinely smooth
hypersurfaces. Negative-twist H0/H1 vanishings remain explicit inputs.
-/
module
public import NcCubic.Geometry.HypersurfaceRestrictionSections
public import NcCubic.Geometry.ImmersionBivector
public import NcCubic.Geometry.ImmersionFaithfulness
public import NcCubic.Geometry.ProjectiveTangent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
attribute [local instance] HasDerivedCategory.standard
namespace NcCubic.Geometry.AmbientBivectorLift
open HypersurfaceSection HypersurfaceRestrictionSequence HypersurfaceRestrictionSections
open Stacks.AlgebraicGeometry.ProjPolyChart
open AlgebraicGeometry.ProjectiveSpectrum.Proj
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ambientBivector (n : ℕ) : (ambient n).Modules :=
  bivectorSheaf (CotangentCoordinates.ambientProjection n)

lemma ambientBivector_locallyFreeOfRank (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (ambientBivector n) (n.choose 2) := by
  let := ProjectiveCohomology.tangentSheaf_locallyFreeOfRank n
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
    (ProjectiveCohomology.tangentSheaf n) n 2

lemma ambientBivector_finiteLocallyFree (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (ambientBivector n) :=
  (ambientBivector_locallyFreeOfRank n).isFiniteLocallyFree

/-- A sheaf morphism on the closed source acts linearly on its actual sections,
with the coefficient action induced from its direct image. -/
def pushedSectionsLinearMap {Y X : Scheme.{u}} (i : Y ⟶ X) {M N : Y.Modules} (φ : M ⟶ N) :
    letI := pushforwardTopModule i M
    letI := pushforwardTopModule i N
    Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤) :=
  ((Stacks.Cohomology.sectionsFunctor X ⊤).map ((Scheme.Modules.pushforward i).map φ)).hom

lemma pushedSectionsLinearMap_apply {Y X : Scheme.{u}} (i : Y ⟶ X)
    {M N : Y.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    pushedSectionsLinearMap i φ s = φ.app ⊤ s := rfl

/-- Canonical image of a genuine bivector under the actual differential of the immersion. -/
def projectiveImageLinearMap {n : ℕ} {Y : Scheme.{0}} (i : Y ⟶ ambient n) :
    letI := pushforwardTopModule i
      (bivectorSheaf (i ≫ CotangentCoordinates.ambientProjection n))
    letI := pushforwardTopModule i ((Scheme.Modules.pullback i).obj (ambientBivector n))
    AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n) →ₗ[Γ(ambient n, ⊤)]
      Γ((Scheme.Modules.pullback i).obj (ambientBivector n), ⊤) :=
  pushedSectionsLinearMap i (ImmersionBivector.projectiveBivectorMap i)

lemma projectiveImageLinearMap_apply {n : ℕ} {Y : Scheme.{0}} (i : Y ⟶ ambient n)
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    projectiveImageLinearMap i π = ImmersionBivector.projectiveImageSection i π := rfl

/-- The actual ambient lift of a genuine hypersurface bivector. Negative-twist
cohomology vanishings are explicit inputs, never representation oracles. -/
def ambientLiftLinearMap {n : ℕ} {Y : Scheme.{0}} (i : Y ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj
      (twisted n (ambientBivector n))))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj
      (twisted n (ambientBivector n)))) :
    letI := pushforwardTopModule i
      (bivectorSheaf (i ≫ CotangentCoordinates.ambientProjection n))
    AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n) →ₗ[Γ(ambient n, ⊤)]
      AlgebraicBivector (CotangentCoordinates.ambientProjection n) := by
  letI := pushforwardTopModule i
    (bivectorSheaf (i ≫ CotangentCoordinates.ambientProjection n))
  letI := pushforwardTopModule i ((Scheme.Modules.pullback i).obj (ambientBivector n))
  exact (cubicRestrictionSectionsEquiv i F hF0 hideal (ambientBivector n)
    (ambientBivector_finiteLocallyFree n) h0 h1).symm.toLinearMap.comp (projectiveImageLinearMap i)

lemma ambientLiftLinearMap_restrict {n : ℕ} {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj
      (twisted n (ambientBivector n))))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj
      (twisted n (ambientBivector n))))
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (ambientBivector n)).app ⊤
      (ambientLiftLinearMap i F hF0 hideal h0 h1 π) =
      ImmersionBivector.projectiveImageSection i π := by
  exact (cubicRestrictionSectionsEquiv i F hF0 hideal (ambientBivector n)
    (ambientBivector_finiteLocallyFree n) h0 h1).apply_symm_apply _

lemma existsUnique_ambientBivector_lift {n : ℕ} {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj
      (twisted n (ambientBivector n))))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj
      (twisted n (ambientBivector n))))
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) :
    ∃! t : AlgebraicBivector (CotangentCoordinates.ambientProjection n),
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (ambientBivector n)).app ⊤ t =
        ImmersionBivector.projectiveImageSection i π :=
  existsUnique_cubicRestriction_lift i F hF0 hideal (ambientBivector n)
    (ambientBivector_finiteLocallyFree n) h0 h1 (ImmersionBivector.projectiveImageSection i π)
/-- On a genuinely smooth closed subvariety, the actual ambient lift is faithful. -/
lemma ambientLiftLinearMap_injective {n : ℕ} {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    [Smooth (i ≫ CotangentCoordinates.ambientProjection n)]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj
      (twisted n (ambientBivector n))))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj
      (twisted n (ambientBivector n)))) :
    Function.Injective (ambientLiftLinearMap i F hF0 hideal h0 h1) := by
  intro π ρ h
  apply ImmersionFaithfulness.projectiveImageSection_injective i
  have he := congrArg
    (fun t : AlgebraicBivector (CotangentCoordinates.ambientProjection n) =>
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (ambientBivector n)).app ⊤ t) h
  exact (ambientLiftLinearMap_restrict i F hF0 hideal h0 h1 π).symm.trans
    (he.trans (ambientLiftLinearMap_restrict i F hF0 hideal h0 h1 ρ))

lemma ambientLiftLinearMap_ne_zero {n : ℕ} {Y : Scheme.{0}}
    (i : Y ⟶ ambient n) [IsClosedImmersion i]
    [Smooth (i ≫ CotangentCoordinates.ambientProjection n)]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (h0 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 0).obj
      (twisted n (ambientBivector n))))
    (h1 : IsZero (((Stacks.Cohomology.sectionsFunctor (ambient n) ⊤).rightDerived 1).obj
      (twisted n (ambientBivector n))))
    (π : AlgebraicBivector (i ≫ CotangentCoordinates.ambientProjection n)) (hπ : π ≠ 0) :
    ambientLiftLinearMap i F hF0 hideal h0 h1 π ≠ 0 := by
  intro h
  have he : ambientLiftLinearMap i F hF0 hideal h0 h1 π =
      ambientLiftLinearMap i F hF0 hideal h0 h1 0 := h.trans (map_zero _).symm
  exact hπ (ambientLiftLinearMap_injective i F hF0 hideal h0 h1 he)

end NcCubic.Geometry.AmbientBivectorLift
