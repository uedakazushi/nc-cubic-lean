module
public import NcCubic.Geometry.ImmersionBivector
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ExteriorPowerMono
public import Mathlib.Algebra.Module.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk
set_option backward.isDefEq.respectTransparency false
universe u
namespace NcCubic.Geometry.ImmersionFaithfulness
variable {X : Scheme.{u}}

/-- The cotangent map of an actual closed immersion is epimorphic. -/
theorem epi_cotangentMap {P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    [IsClosedImmersion i] : Epi (ImmersionBivector.cotangentMap i p) := by
  obtain ⟨h, he⟩ := Scheme.Hom.toRelativeDifferentials_exact i p
  have hz := Scheme.Hom.isZero_relativeDifferentials_of_formallyUnramified i
  exact he.epi_f (hz.eq_of_tgt _ _)

/-- An epimorphism onto a locally free cotangent module splits at each stalk;
its actual sheaf-dual map therefore has a stalkwise retraction. -/
theorem dual_stalk_retraction {M N : X.Modules} (f : M ⟶ N) (hf : Epi f)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} N) (x : X) :
    ∃ r : modStalk (dualSheaf M) x →ₗ[ringStalk X.sheaf x] modStalk (dualSheaf N) x,
      r ∘ₗ stalkHom (dualMap f) x = LinearMap.id := by
  have : M.IsFinitePresentation := PullbackDual.isFinitePresentation_of_isFiniteLocallyFree M hM
  have : N.IsFinitePresentation := PullbackDual.isFinitePresentation_of_isFiniteLocallyFree N hN
  have : Module.Free (ringStalk X.sheaf x) (modStalk N x) :=
    (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree N x).1
  obtain ⟨s, hs⟩ := (stalkHom f x).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (surjective_stalkHom f hf x))
  let r := (dualStalkEquiv N x).symm.toLinearMap ∘ₗ
    (s.dualMap ∘ₗ (dualStalkEquiv M x).toLinearMap)
  refine ⟨r, ?_⟩
  apply LinearMap.ext
  intro ψ
  apply (dualStalkEquiv N x).injective
  change (dualStalkEquiv N x) ((dualStalkEquiv N x).symm
    (s.dualMap ((dualStalkEquiv M x) (stalkHom (dualMap f) x ψ)))) =
      (dualStalkEquiv N x) ψ
  erw [LinearEquiv.apply_symm_apply]
  change s.dualMap ((dualStalkEquiv M x) (stalkHom (dualMap f) x ψ)) =
    (dualStalkEquiv N x) ψ
  apply LinearMap.ext
  intro n
  change dualStalkEquiv M x (stalkHom (dualMap f) x ψ) (s n) = dualStalkEquiv N x ψ n
  rw [dualStalkEquiv_stalkHom_dualMap]
  exact congrArg (dualStalkEquiv N x ψ) (LinearMap.congr_fun hs n)

/-- The two standard spellings of the commutative-ring stalk map agree. -/
theorem stalkMapL_eq_stalkHom {M N : X.Modules} (f : M ⟶ N) (x : X) :
    PresheafOfModules.stalkMapL (R := X.presheaf) x f.val = stalkHom f x := by
  ext m
  exact (SheafOfModules.stalkMap_hom_eq_stalkMapL x f m).symm.trans
    (stalkMap_apply_eq_stalkHom f x m)

/-- Exterior powers of the dual of an epimorphism between vector bundles
are monomorphisms, with no splitting hypothesis supplied by the caller. -/
theorem mono_exterior_dual_of_epi {M N : X.Modules} (f : M ⟶ N) (hf : Epi f)
    (hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M)
    (hN : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} N) (n : ℕ) :
    Mono (Scheme.Modules.exteriorPowerMap (dualMap f) (n : ℤ)) := by
  apply SheafOfModules.mono_pieceMap_of_stalkMapL_retraction
    (Osharp := X.sheaf)
    (Scheme.Modules.exteriorGenerator (dualSheaf N))
    (Scheme.Modules.exteriorGenerator (dualSheaf M))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (dualSheaf N))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (dualSheaf M))
  intro x
  obtain ⟨r, hr⟩ := dual_stalk_retraction f hf hM hN x
  exact ⟨r, by erw [stalkMapL_eq_stalkHom]; exact hr⟩

/-- The actual immersion multivector map preserves sections whenever the
cotangent map is onto and the two cotangent bundles are locally free. -/
theorem mono_multivectorMap {P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (hX : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials (i ≫ p)))
    [IsClosedImmersion i] (n : ℕ) :
    Mono (ImmersionBivector.multivectorMap i p hP (n : ℤ)) := by
  have hpb := PullbackDual.isFiniteLocallyFree_pullback i
    (Scheme.Hom.relativeDifferentials p) hP
  have := mono_exterior_dual_of_epi (ImmersionBivector.cotangentMap i p) (epi_cotangentMap i p) hpb hX n
  unfold ImmersionBivector.multivectorMap ImmersionBivector.exteriorAlongPullback
    ImmersionBivector.tangentMap
  rw [Scheme.Modules.exteriorPowerMap_comp]
  infer_instance

/-- Faithfulness on local bivectors follows from the actual immersion map. -/
theorem imageSection_injective {P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hP : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (hX : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials (i ≫ p)))
    [IsClosedImmersion i] (U : X.Opens) :
    Function.Injective (ImmersionBivector.imageSection i p hP U) := by
  have : Mono (ImmersionBivector.bivectorMap i p hP) := mono_multivectorMap i p hP hX 2
  have : Mono (ImmersionBivector.bivectorMap i p hP).val :=
    (SheafOfModules.forget X.ringCatSheaf).map_mono
      (ImmersionBivector.bivectorMap i p hP)
  exact PresheafOfModules.injective_of_mono _ (.op U)

/-- Nonzero global bivectors on a smooth projective subvariety remain nonzero
under the canonical immersion into the ambient tangent exterior square. -/
theorem projectiveImageSection_injective {n : ℕ} {Y : Scheme.{0}}
    (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    [Smooth (i ≫ CotangentCoordinates.ambientProjection n)] :
    Function.Injective (ImmersionBivector.projectiveImageSection i) := by
  exact imageSection_injective i (CotangentCoordinates.ambientProjection n)
    (CotangentCoordinates.projectiveCotangent_locallyFreeOfRank n).isFiniteLocallyFree
    (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials _) ⊤

end NcCubic.Geometry.ImmersionFaithfulness
