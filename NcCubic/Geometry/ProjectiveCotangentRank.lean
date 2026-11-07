/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Uses the pinned Stacks affine computation of cotangent sections and actual
projective polynomial charts. The finite-basis local-rank adapter is adapted from
StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.FiniteDegree at revision
5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache 2.0). -/
module
public import NcCubic.Geometry.AmbientChartAlgebra
public import NcCubic.Geometry.PolynomialKahlerBasis
public import NcCubic.Geometry.OpenPullbackSections
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentBijective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace NcCubic.Geometry.CotangentCoordinates
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

abbrev cotangentChartOpen (i : Fin (n+1)) : (ProjectiveAmbient n).Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)

abbrev ambientProjection (n : ℕ) :=
  Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n

theorem cotangentChartOpen_affine (i : Fin (n+1)) : IsAffineOpen (cotangentChartOpen i) :=
  Proj.isAffineOpen_basicOpen _ _ (Stacks.ProjectiveChart.X_mem_degree_one ℂ i) (by omega)

/-- The actual projective chart has `n` Kähler coordinate differentials over
its genuine base section ring, not only over an abstract copy of ℂ. -/
def projectiveChartKahlerBasis (i : Fin (n+1)) :
    letI : Algebra Γ(Spec (CommRingCat.of ℂ), ⊤) Γ(ProjectiveAmbient n, cotangentChartOpen i) :=
      Stacks.Smooth.algebraAppLE (ambientProjection n) (le_top : cotangentChartOpen i ≤ _)
    Module.Basis (Fin n) Γ(ProjectiveAmbient n, cotangentChartOpen i)
      Ω[Γ(ProjectiveAmbient n, cotangentChartOpen i)⁄Γ(Spec (CommRingCat.of ℂ), ⊤)] := by
  let U := cotangentChartOpen i
  let p := ambientProjection n
  letI : Algebra Γ(Spec (CommRingCat.of ℂ), ⊤) Γ(ProjectiveAmbient n, U) :=
    Stacks.Smooth.algebraAppLE p (le_top : U ≤ _)
  letI : Algebra ℂ Γ(ProjectiveAmbient n, U) :=
    (AffineSmoothness.coefficientMap p U).toAlgebra
  let eBase := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  have hbase : ∀ l : Γ(Spec (CommRingCat.of ℂ), ⊤),
      algebraMap Γ(Spec (CommRingCat.of ℂ), ⊤) Γ(ProjectiveAmbient n, U) l =
        algebraMap ℂ Γ(ProjectiveAmbient n, U) (eBase l) := by
    intro l
    change (p.appLE ⊤ U le_top).hom l =
      (p.appLE ⊤ U le_top).hom (eBase.symm (eBase l))
    rw [eBase.symm_apply_apply]
  exact (polynomialKahlerBasis (ambientSectionsChartAlgEquiv i)).map
    (kaehlerBaseEquiv eBase hbase).symm

/-- The affine cotangent computation gives an actual chart basis of the
pullback cotangent sheaf, without using the general smooth-differentials theorem. -/
def projectivePullbackCotangentBasis (i : Fin (n+1)) :
    Module.Basis (Fin n) Γ((cotangentChartOpen i : Scheme), ⊤)
      Γ((Scheme.Modules.pullback (cotangentChartOpen i).ι).obj
        (Stacks.Smooth.cotangentSheaf (ambientProjection n)), ⊤) := by
  let U := cotangentChartOpen i
  let p := ambientProjection n
  have hU : IsAffineOpen U := cotangentChartOpen_affine i
  have : IsAffine (U : Scheme) := hU
  letI : Algebra Γ(Spec (CommRingCat.of ℂ), ⊤) Γ(ProjectiveAmbient n, U) :=
    Stacks.Smooth.algebraAppLE p (le_top : U ≤ _)
  letI : Algebra Γ(ProjectiveAmbient n, U) Γ((U : Scheme), ⊤) :=
    Stacks.Smooth.algebraAppLE U.ι (le_of_eq U.ι_preimage_self.symm)
  exact ((projectiveChartKahlerBasis i).baseChange Γ((U : Scheme), ⊤)).map
    (Stacks.Smooth.cotangentComparisonEquiv p U.ι (isAffineOpen_top _)
      hU (le_top : U ≤ _) (le_of_eq U.ι_preimage_self.symm))

/-- The genuine relative cotangent sheaf has its coordinate basis on every
standard affine chart. -/
def projectiveCotangentChartBasis (i : Fin (n+1)) :
    Module.Basis (Fin n) Γ(ProjectiveAmbient n, cotangentChartOpen i)
      Γ(Scheme.Hom.relativeDifferentials (ambientProjection n), cotangentChartOpen i) := by
  let U := cotangentChartOpen i
  let p := ambientProjection n
  have b : Module.Basis (Fin n) Γ(ProjectiveAmbient n, U)
      Γ(Stacks.Smooth.cotangentSheaf p, U) := by
    exact Eq.mp (congrArg (fun W : (ProjectiveAmbient n).Opens =>
      Module.Basis (Fin n) Γ(ProjectiveAmbient n, W)
        Γ(Stacks.Smooth.cotangentSheaf p, W)) U.ι_image_top)
      (openPullbackSectionsBasis U.ι (Stacks.Smooth.cotangentSheaf p)
        (projectivePullbackCotangentBasis i))
  exact b.map (moduleSectionsLinearEquiv (Scheme.Hom.cotangentSheafIso p).symm U)

/-- The one-element principal cover turns a finite basis into actual finite
local-rank data (focused version of the pinned Stacks field-descent helper). -/
private theorem finBasis_locallyFreeOfRank {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {r : ℕ} (b : Module.Basis (Fin r) R M) :
    Module.IsFiniteLocallyFreeOfRank R M r := by
  classical
  refine ⟨PUnit, fun _ => 1, by simp, fun _ => ?_⟩
  let : Algebra R (Localization.Away (1 : R)) :=
    @OreLocalization.instAlgebra R _ (Submonoid.powers (1 : R)) _ R _ (Algebra.id R)
  have : IsLocalization (Submonoid.powers (1 : R)) (Localization.Away (1 : R)) :=
    Localization.isLocalization (R := R) (M := Submonoid.powers 1)
  exact ⟨b.ofIsLocalizedModule (Localization.Away (1 : R)) (Submonoid.powers (1 : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (1 : R)) M)⟩

/-- Projective cotangent rank follows from actual affine polynomial bases.
No smoothness or cotangent-local-freeness assumption is supplied by the caller. -/
theorem projectiveCotangent_locallyFreeOfRank (n : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (Scheme.Hom.relativeDifferentials (ambientProjection n)) n := by
  let M := Scheme.Hom.relativeDifferentials (ambientProjection n)
  have : M.IsQuasicoherent := Scheme.Hom.isQuasicoherent_relativeDifferentials _
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M n).mp
    (Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens M n fun x => ?_)
  have hx : x ∈ (⨆ i : Fin (n+1), cotangentChartOpen i) := by
    rw [show (⨆ i : Fin (n+1), cotangentChartOpen i) = ⊤ from
      Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top ℂ n]
    trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨⟨cotangentChartOpen i, cotangentChartOpen_affine i⟩, hxi,
    finBasis_locallyFreeOfRank (projectiveCotangentChartBasis i)⟩

end NcCubic.Geometry.CotangentCoordinates
