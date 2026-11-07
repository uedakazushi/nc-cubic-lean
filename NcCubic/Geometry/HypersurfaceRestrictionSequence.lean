/-
The genuine hypersurface restriction sequence for a finite locally free module.
The first map is explicitly multiplication by the cubic section after cancelling
O(-3) tensor O(3). The last map is literally the pullback-pushforward adjunction
unit for the original closed immersion.
The arbitrary-factor cokernel and explicit Mono helper patterns are adapted
from pinned Stacks Divisors/ZeroSchemeExactSequenceTwist (Tag 0C6K).
-/
module
public import NcCubic.Geometry.RestrictionIsoTransport
public import NcCubic.Geometry.HypersurfaceSection
public import NcCubic.Geometry.ModulesBridge
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.IdealSheafOfHypersurface
public import NcCubic.Geometry.ProjectiveTwistInverse
public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Basic
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
universe u
namespace NcCubic.Geometry.HypersurfaceRestrictionSequence
local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property
local instance (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorSymmetric X.sheaf.obj X.ringCatSheaf.property

lemma tensorLeft_preservesFiniteLimits_of_flat (X : Scheme.{u}) (M : X.Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) M) :
    PreservesFiniteLimits (tensorLeft M) := by
  have hflat := (exactFunctor_iff _).mp hM
  let : PreservesFiniteLimits (tensorRight M) := hflat.1
  exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

lemma shortExact_unit_transport {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {A B B' : C} (f : A ⟶ B) (w : f ≫ adj.unit.app B = 0)
    (hSE : (ShortComplex.mk f (adj.unit.app B) w).ShortExact) (e : B ≅ B') :
    ∃ w' : (f ≫ e.hom) ≫ adj.unit.app B' = 0,
      (ShortComplex.mk (f ≫ e.hom) (adj.unit.app B') w').ShortExact := by
  have hn : e.hom ≫ adj.unit.app B' = adj.unit.app B ≫ (F ⋙ G).map e.hom :=
    adj.unit.naturality e.hom
  have hw : (f ≫ e.hom) ≫ adj.unit.app B' = 0 := by
    rw [Category.assoc, hn, ← Category.assoc, w, zero_comp]
  refine ⟨hw, ShortComplex.shortExact_of_iso ?_ hSE⟩
  exact ShortComplex.isoMk (Iso.refl A) e ((F ⋙ G).mapIso e) (by simp) hn

private lemma mono_of_isIso' {C : Type*} [Category C] {A B : C}
    (f : A ⟶ B) (hf : IsIso f) : Mono f := by
  have := hf
  infer_instance
private lemma mono_map' {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    [T.PreservesMonomorphisms] {A B : C} (f : A ⟶ B) (hf : Mono f) : Mono (T.map f) := by
  have := hf
  infer_instance
private lemma mono_comp' {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (hf : Mono f) (hg : Mono g) : Mono (f ≫ g) := by
  have := hf
  have := hg
  infer_instance

lemma shortExact_zeroScheme_twist_of_preservesMonos (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    (M : X.Modules) [(tensorLeft M).PreservesMonomorphisms] :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let f : M ⟶ M ⊗ L := (ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s
    ∃ w : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L) = 0,
      (ShortComplex.mk f
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L)) w).ShortExact := by
  dsimp only
  have hf : Mono ((ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s) :=
    mono_comp' _ _ (mono_of_isIso' _ inferInstance)
      (mono_map' (tensorLeft M) (L.unitHomEquiv.symm s) hs)
  obtain ⟨e, he⟩ := exists_cokernelIso_unit_zeroScheme_twist' X L s M
  exact ShortComplex.shortExact_of_cokernelIso _ hf e he

lemma shortExact_zeroScheme_twist_of_flat (X : Scheme.{u}) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections) (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s)
    (M : X.Modules) (hM : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) M) :
    let i := (zeroScheme X L (s.eval (op ⊤))).subschemeι
    let f : M ⟶ M ⊗ L := (ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s
    ∃ w : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L) = 0,
      (ShortComplex.mk f
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L)) w).ShortExact := by
  let := tensorLeft_preservesFiniteLimits_of_flat X M hM
  exact shortExact_zeroScheme_twist_of_preservesMonos X L s hs M

open Stacks.AlgebraicGeometry.ProjPolyChart
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistRank

attribute [local instance] MvPolynomial.gradedAlgebra
open HypersurfaceSection
abbrev twisted (n : ℕ) (M : (ambient n).Modules) : (ambient n).Modules :=
  (Stacks.AlgebraicGeometry.ProjTwistFunctor.twistFunctor (polyGrading ℂ n) (-3)).obj M

def twistNegTensorIsoUnit (n : ℕ) :
    (twist n (-3) ⊗ twist n 3 : (ambient n).Modules) ≅
      SheafOfModules.unit (ambient n).ringCatSheaf := by
  let e : (((Stacks.SheafOfModules.Tensor.sheafTensor (ambient n).sheaf).obj
      (twist n (-3))).obj (twist n 3)) ≅
      SheafOfModules.unit (ambient n).ringCatSheaf :=
    (by simpa only [neg_add_cancel] using tensorTwistingSheafIso ℂ n (-3) 3) ≪≫
      Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading ℂ n)
  exact (schemeModulesOfSite (ambient n)).mapIso e

def untwistAfterCubicIso (n : ℕ) (M : (ambient n).Modules) :
    (twisted n M ⊗ twist n 3 : (ambient n).Modules) ≅ M :=
  (α_ M (twist n (-3)) (twist n 3)) ≪≫
    (tensorLeft M).mapIso (twistNegTensorIsoUnit n) ≪≫ (ρ_ M)

def cubicRestrictionInjection {n : ℕ} (F : polyGrading ℂ n 3) (M : (ambient n).Modules) :
    twisted n M ⟶ M :=
  ((ρ_ (twisted n M)).inv ≫ (twisted n M) ◁ (twist n 3).unitHomEquiv.symm (cubicSection F)) ≫
    (untwistAfterCubicIso n M).hom

/-- The actual hypersurface restriction sequence, with its last map exactly the
canonical pullback-pushforward adjunction unit for the original closed immersion. -/
theorem cubicRestriction_shortExact {n : ℕ} {Z : Scheme.{0}}
    (i : Z ⟶ ambient n) [IsClosedImmersion i]
    (F : polyGrading ℂ n 3) (hF0 : (F : MvPolynomial (Fin (n+1)) ℂ) ≠ 0)
    (hideal : idealOfClosedSubscheme (polyGrading ℂ n) i = Ideal.span {(F : MvPolynomial _ ℂ)})
    (M : (ambient n).Modules)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M) :
    ∃ w : cubicRestrictionInjection F M ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M = 0,
      (ShortComplex.mk (cubicRestrictionInjection F M)
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) w).ShortExact := by
  let hgen := MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) ℂ
  let : AlgebraicGeometry.SheafOfModules.IsInvertible (ambient n).sheaf.obj
      (ambient n).ringCatSheaf.property (twist n 3) :=
    algebraicGeometry_isInvertible_twistingSheaf (polyGrading ℂ n) hgen 3
  let : AlgebraicGeometry.SheafOfModules.IsInvertible (ambient n).sheaf.obj
      (ambient n).ringCatSheaf.property (twist n (-3)) :=
    algebraicGeometry_isInvertible_twistingSheaf (polyGrading ℂ n) hgen (-3)
  let : PreservesFiniteLimits (tensorLeft M) := tensorLeft_preservesFiniteLimits_of_flat _ M
    (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree M hM)
  let : (tensorLeft (twist n (-3))).IsEquivalence :=
    AlgebraicGeometry.isEquivalence_tensorLeft (ambient n) (twist n (-3))
  let : PreservesFiniteLimits (tensorLeft (twisted n M)) :=
    preservesFiniteLimits_of_natIso (tensorLeftTensor M (twist n (-3))).symm
  have hs0 := HypersurfaceSection.cubicSection_eval_ne_zero F hF0
  have hs := isRegularSection_of_eval_top_ne_zero (twist n 3) (cubicSection F) hs0
  let C := zeroScheme (ambient n) (twist n 3) ((cubicSection F).eval (op ⊤))
  let j := C.subschemeι
  have hk : i.ker = C := HypersurfaceSection.ker_eq_zeroScheme i F hideal
  have hker : i.ker = j.ker := hk.trans C.ker_subschemeι.symm
  obtain ⟨w0,h0⟩ := shortExact_zeroScheme_twist_of_preservesMonos
    (ambient n) (twist n 3) (cubicSection F) hs (twisted n M)
  obtain ⟨w1,h1⟩ := shortExact_unit_transport
    (Scheme.Modules.pullbackPushforwardAdjunction j) _ w0 h0 (untwistAfterCubicIso n M)
  exact RestrictionIsoTransport.shortExact_of_ker_eq i j hker
    (cubicRestrictionInjection F M) w1 h1

end NcCubic.Geometry.HypersurfaceRestrictionSequence
