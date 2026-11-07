/- Actual restriction along a scheme isomorphism of the closed source.
The comparison isomorphism intertwines the literal pullback-pushforward units,
so short exact restriction sequences transport without changing their last map. -/
module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.ShortExact
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace NcCubic.Geometry.RestrictionIsoTransport
lemma pushforward_isEquivalence {Z Y : Scheme.{u}} (e : Z ≅ Y) :
    (Scheme.Modules.pushforward e.hom).IsEquivalence :=
  Functor.IsEquivalence.mk' (Scheme.Modules.pushforward e.inv)
    (Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
      Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫ Scheme.Modules.pushforwardId Z).symm
    (Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
      Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Y)

def restrictionComparison {Z Y X : Scheme.{u}} (e : Z ≅ Y) (j : Y ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj M) ≅
      (Scheme.Modules.pushforward (e.hom ≫ j)).obj
        ((Scheme.Modules.pullback (e.hom ≫ j)).obj M) := by
  let := pushforward_isEquivalence e
  exact (Scheme.Modules.pushforward j).mapIso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app
      ((Scheme.Modules.pullback j).obj M))) ≪≫
    (Scheme.Modules.pushforwardComp e.hom j).app
      ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback j).obj M)) ≪≫
    (Scheme.Modules.pushforward (e.hom ≫ j)).mapIso
      ((Scheme.Modules.pullbackComp e.hom j).app M)

lemma unit_restrictionComparison {Z Y X : Scheme.{u}} (e : Z ≅ Y)
    (j : Y ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M ≫
      (restrictionComparison e j M).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (e.hom ≫ j)).unit.app M := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction j).comp
      (Scheme.Modules.pullbackPushforwardAdjunction e.hom))
    (Scheme.Modules.pullbackPushforwardAdjunction (e.hom ≫ j))
    (Scheme.Modules.pullbackComp e.hom j).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hh := congrArg
    (fun f => f ≫ (Scheme.Modules.pushforward (e.hom ≫ j)).map
      ((Scheme.Modules.pullbackComp e.hom j).hom.app M)) h
  simpa [restrictionComparison, Adjunction.comp_unit_app, Category.assoc] using hh

lemma shortExact_comp_iso {Z Y X : Scheme.{u}} (e : Z ≅ Y) (j : Y ⟶ X)
    {A M : X.Modules} (f : A ⟶ M)
    (w : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M = 0)
    (hSE : (ShortComplex.mk f
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M) w).ShortExact) :
    ∃ w' : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction (e.hom ≫ j)).unit.app M = 0,
      (ShortComplex.mk f
        ((Scheme.Modules.pullbackPushforwardAdjunction (e.hom ≫ j)).unit.app M) w').ShortExact := by
  have hw : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction (e.hom ≫ j)).unit.app M = 0 := by
    rw [← unit_restrictionComparison e j M, ← Category.assoc, w, zero_comp]
  refine ⟨hw, ShortComplex.shortExact_of_iso ?_ hSE⟩
  exact ShortComplex.isoMk (Iso.refl A) (Iso.refl M) (restrictionComparison e j M)
    (by simp) (by simpa using (unit_restrictionComparison e j M).symm)
/-- Equal actual ideal sheaves give the same restriction sequence, with the
canonical unit for the original closed immersion retained verbatim. -/
lemma shortExact_of_ker_eq {Z Y X : Scheme.{u}} (i : Z ⟶ X) (j : Y ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (hker : i.ker = j.ker)
    {A M : X.Modules} (f : A ⟶ M)
    (w : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M = 0)
    (hSE : (ShortComplex.mk f
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M) w).ShortExact) :
    ∃ w' : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M = 0,
      (ShortComplex.mk f
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M) w').ShortExact := by
  let e := IsClosedImmersion.lift j i hker.symm.le
  have he : e ≫ j = i := IsClosedImmersion.lift_fac _ _ _
  have : IsIso e := IsClosedImmersion.isIso_of_ker_eq i j e he hker
  have hh := shortExact_comp_iso (asIso e) j f w hSE
  change ∃ w' : f ≫ (Scheme.Modules.pullbackPushforwardAdjunction (e ≫ j)).unit.app M = 0,
    (ShortComplex.mk f
      ((Scheme.Modules.pullbackPushforwardAdjunction (e ≫ j)).unit.app M) w').ShortExact at hh
  rw [he] at hh
  exact hh

end NcCubic.Geometry.RestrictionIsoTransport

