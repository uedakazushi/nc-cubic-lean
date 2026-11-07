/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
The pointwise coefficient comparison follows the argument in
StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsLinear
at the pinned Stacks revision (Apache 2.0; dependency LICENSE).
-/
module
public import NcCubic.Geometry.AmbientProjectivePoisson
public import NcCubic.Geometry.PoissonGluing
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
@[expose] public section
noncomputable section
open AlgebraicGeometry
namespace NcCubic.Geometry.HomogeneousBasic
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {N : ℕ}

/-- The genuine constant degree-zero homogeneous fraction. -/
def constant {h : CubicPolynomial N} {d : ℕ} (hh : h.IsHomogeneous d) (c : ℂ) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h :=
  HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin N) ℂ) hh 0 (C c) (by
    rw [zero_nsmul]
    change (C c : CubicPolynomial N).IsHomogeneous 0
    exact isHomogeneous_C (σ:=Fin N) c)

@[simp] theorem constant_val {h : CubicPolynomial N} {d : ℕ}
    (hh : h.IsHomogeneous d) (c : ℂ) :
    (constant hh c).val = algebraMap (CubicPolynomial N) (Localization.Away h) (C c) := by
  change Localization.mk (C c : CubicPolynomial N) (1 : Submonoid.powers h) = _
  rw [Localization.mk_one_eq_algebraMap]

/-- Constant fractions are central for every homogeneous quadratic coefficient bracket. -/
theorem bracket_constant_right
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) (c : ℂ) :
    bracket q hq hd hh x (constant hh c) = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [bracket_val,constant_val,HomogeneousLocalization.val_zero]
  simp [LocalizedPoisson.bracket,LocalizedPoisson.localizedPderiv]
end NcCubic.Geometry.HomogeneousBasic

namespace NcCubic.Geometry.HomogeneousSections
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

/-- The canonical actual section associated to a scalar constant. -/
def constant {h : CubicPolynomial (n+1)} {d : ℕ}
    (hd : 0 < d) (hh : h.IsHomogeneous d) (c : ℂ) :=
  homogeneousSectionsEquiv hh hd (HomogeneousBasic.constant hh c)

/-- The actual homogeneous-basic-open section bracket annihilates the
canonical scalar sections. Identification with the chosen structure morphism
is a separate coefficient-map comparison. -/
theorem bracket_constant_right
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1)) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (a : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) (c : ℂ) :
    bracket q hq hd hh a (constant hd hh c) = 0 := by
  let E := homogeneousSectionsEquiv hh hd
  obtain ⟨a,rfl⟩ := E.surjective a
  simp only [constant,E,bracket_equiv,HomogeneousBasic.bracket_constant_right,map_zero]
end NcCubic.Geometry.HomogeneousSections

namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 600000
variable {n : ℕ}

/-- Canonical homogeneous constant sections are exactly the coefficients
pulled back along the genuine projective-space structure morphism. -/
theorem homogeneous_coefficientMap_eq_constant
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d) (c : ℂ) :
    AffineSmoothness.coefficientMap
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)
      (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h) c =
      HomogeneousSections.constant hd hh c := by
  refine Subtype.ext (funext fun p => HomogeneousLocalization.val_injective _ ?_)
  change HomogeneousLocalization.val
    ((((Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n).appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)).1 ⟨p.1,trivial⟩) = _
  rw [Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val]
  change _ = HomogeneousLocalization.val
    (((Proj.awayToSection (homogeneousSubmodule (Fin (n+1)) ℂ) h).hom
      (HomogeneousBasic.constant hh c)).1 p)
  refine Eq.trans ?_ (ProjectiveSpectrum.Proj.awayToSection_apply
    (homogeneousSubmodule (Fin (n+1)) ℂ) h (HomogeneousBasic.constant hh c) p).symm
  rw [HomogeneousBasic.constant_val,IsLocalization.map_eq]
  rfl

/-- The genuinely glued every-open projective Poisson bracket is relative
to the actual structure morphism to Spec ℂ. -/
theorem ambientProjectivePoisson_relative
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2) (hskew : ∀ i j,q j i = -q i j)
    (hJac : SatisfiesJacobi (bracketFromCoefficients q)) :
    (ambientProjectivePoisson q hq hskew hJac).IsRelative
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) := by
  apply (ambientBasisPoisson q hq hskew hJac).glued_relative
  intro i a c
  have hi : (i.2 : CubicPolynomial (n+1)).IsHomogeneous (i.1 : ℕ) := i.2.property
  change HomogeneousSections.bracket q hq i.1.pos hi a
    (AffineSmoothness.coefficientMap _
      (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) (i.2 : CubicPolynomial (n+1))) c) = 0
  rw [homogeneous_coefficientMap_eq_constant i.1.pos hi]
  exact HomogeneousSections.bracket_constant_right q hq i.1.pos hi a c

/-- The original contraction tensor gives a genuine complex-relative
Poisson operation on every projective open. -/
theorem contractionProjectivePoisson_relative
    (F : CubicPolynomial (n+1)) (P : Trivector (n+1)) (hF : F.IsHomogeneous 3)
    (hJac : SatisfiesJacobi (bracketFromCoefficients (contractionCoefficients F P))) :
    (contractionProjectivePoisson F P hF hJac).IsRelative
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n) :=
  ambientProjectivePoisson_relative (contractionCoefficients F P)
    (contractionCoefficients_isHomogeneous F P hF) (contraction_skew F P) hJac
end NcCubic.Geometry
