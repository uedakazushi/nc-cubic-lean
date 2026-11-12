/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorFunctionalBracket
public import NcCubic.Geometry.ContractionFaithfulness
public import NcCubic.Geometry.ProjectiveTangent
public import NcCubic.Geometry.PullbackLocallyFree
public import NcCubic.Geometry.AmbientChartAlgebra
public import NcCubic.Geometry.ProjectiveCoordinateDerivatives
public import Mathlib.Algebra.MvPolynomial.Derivation
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace NcCubic.Geometry
universe u
section Algebra
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {σ : Type*}
/-- Polynomial-chart derivations are determined by their actual coordinate images. -/
theorem derivation_ext_of_polynomial_equiv (e : MvPolynomial σ R ≃ₐ[R] A)
    (d₁ d₂ : Derivation R A A)
    (h : ∀ i, d₁ (e (MvPolynomial.X i)) = d₂ (e (MvPolynomial.X i))) : d₁ = d₂ := by
  apply Derivation.ext
  intro a
  obtain ⟨p, rfl⟩ := e.surjective a
  induction p using MvPolynomial.induction_on with
  | C r =>
    have hc : e (MvPolynomial.C r) = algebraMap R A r := e.commutes r
    simp only [hc, Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, Derivation.leibniz, hp, h i]
end Algebra

section Relative
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of R))

/-- Faithfulness on an affine open uses actual quasicoherent module families;
it controls the whole restricted morphism, not merely arbitrary operations on Γ(U). -/
theorem affine_contractionSection_ext
    [(Scheme.Hom.relativeDifferentials f).IsQuasicoherent] [(tangentSheaf f).IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (c d : Γ(tangentContractionSheaf f,U))
    (h : ∀ a b, contractionSectionBracket f U c a b = contractionSectionBracket f U d a b) :
    c = d := by
  apply (localHomFamily_eval_bijective (Scheme.Hom.relativeDifferentials f)
    (tangentSheaf f) U hU).injective
  apply LinearMap.ext
  intro α
  change contractionEvaluation f U c α = contractionEvaluation f U d α
  exact affine_contractionEvaluation_ext f U hU c d h α

/-- The affine comparison determines the actual restriction on every subopen. -/
theorem affine_contractionSection_restrict_ext
    [(Scheme.Hom.relativeDifferentials f).IsQuasicoherent] [(tangentSheaf f).IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (c d : Γ(tangentContractionSheaf f,U))
    (h : ∀ a b, contractionSectionBracket f U c a b = contractionSectionBracket f U d a b)
    (V : X.Opens) (hVU : V ≤ U) (α : Γ(Scheme.Hom.relativeDifferentials f,V)) :
    contractionEvaluation f V ((tangentContractionSheaf f).val.map (homOfLE hVU).op c) α =
      contractionEvaluation f V ((tangentContractionSheaf f).val.map (homOfLE hVU).op d) α := by
  rw [affine_contractionSection_ext f U hU c d h]

/-- Relative biderivations on a genuine polynomial chart are determined by
coordinate pairs, via two actual Hamiltonian derivations. -/
theorem biderivation_ext_on_polynomial_chart {σ : Type u}
    (B D : StructureSheafBiderivation X) (hB : B.IsRelative f) (hD : D.IsRelative f)
    (U : X.Opens)
    (e : letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
      MvPolynomial σ R ≃ₐ[R] Γ(X,U))
    (h : ∀ i j, B.bracket U (e (MvPolynomial.X i)) (e (MvPolynomial.X j)) =
      D.bracket U (e (MvPolynomial.X i)) (e (MvPolynomial.X j))) :
    ∀ a b : Γ(X,U), B.bracket U a b = D.bracket U a b := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  have hgen (i : σ) (b : Γ(X,U)) : B.bracket U (e (MvPolynomial.X i)) b =
      D.bracket U (e (MvPolynomial.X i)) b := by
    exact congrArg (fun d : Derivation R Γ(X,U) Γ(X,U) => d b)
      (derivation_ext_of_polynomial_equiv e
        (B.hamiltonian f hB U (e (MvPolynomial.X i)))
        (D.hamiltonian f hD U (e (MvPolynomial.X i))) (h i))
  intro a b
  have hd : B.hamiltonian f hB U a = D.hamiltonian f hD U a := by
    apply derivation_ext_of_polynomial_equiv e
    intro i
    exact (B.skew U a (e (MvPolynomial.X i))).trans
      ((congrArg Neg.neg (hgen i a)).trans (D.skew U a (e (MvPolynomial.X i))).symm)
  exact congrArg (fun d : Derivation R Γ(X,U) Γ(X,U) => d b) hd
/-- Equality on all functions of affine chart opens determines the actual
restricted contraction families and hence the biderivation on every open. -/
theorem relative_biderivation_ext_of_affine_cover
    [(Scheme.Hom.relativeDifferentials f).IsQuasicoherent] [(tangentSheaf f).IsQuasicoherent]
    {ι : Type u} (W : ι → X.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hcover : iSup W = ⊤)
    (B D : StructureSheafBiderivation X) (hB : B.IsRelative f) (hD : D.IsRelative f)
    (h : ∀ i (a b : Γ(X,W i)), B.bracket (W i) a b = D.bracket (W i) a b) :
    ∀ (U : X.Opens) (a b : Γ(X,U)), B.bracket U a b = D.bracket U a b := by
  let c := exteriorFunctionalContraction f (biderivationCotangentDualSection f B hB)
  let d := exteriorFunctionalContraction f (biderivationCotangentDualSection f D hD)
  have rb (U : X.Opens) (a b : Γ(X,U)) :
      (contractionGlobalBracket f c).bracket U a b = B.bracket U a b :=
    biderivationFunctionalContraction_bracket f B hB U a b
  have rd (U : X.Opens) (a b : Γ(X,U)) :
      (contractionGlobalBracket f d).bracket U a b = D.bracket U a b :=
    biderivationFunctionalContraction_bracket f D hD U a b
  have hcd : c = d := by
    let C := tangentContractionSheaf f
    let F : TopCat.Sheaf Ab X := ⟨C.presheaf, C.isSheaf⟩
    apply F.eq_of_locally_eq' W ⊤ (fun _ => homOfLE le_top) hcover.ge
    intro i
    apply affine_contractionSection_ext f (W i) (hW i)
    intro a b
    change (contractionGlobalBracket f c).bracket (W i) a b =
      (contractionGlobalBracket f d).bracket (W i) a b
    rw [rb, rd]
    exact h i a b
  intro U a b
  exact (rb U a b).symm.trans
    ((congrArg (fun q => (contractionGlobalBracket f q).bracket U a b) hcd).trans (rd U a b))
end Relative

section Projective
attribute [local instance] MvPolynomial.gradedAlgebra
open ProjectiveCoordinateDerivatives
open MvPolynomial

/-- The actual projective tangent sheaf is quasicoherent, from its proved rank. -/
theorem projective_tangent_isQuasicoherent (n : ℕ) :
    (tangentSheaf (CotangentCoordinates.ambientProjection n)).IsQuasicoherent := by
  have h := ProjectiveCohomology.tangentSheaf_locallyFreeOfRank n
  let : (tangentSheaf (CotangentCoordinates.ambientProjection n)).IsFinitePresentation :=
    PullbackDual.isFinitePresentation_of_isFiniteLocallyFree _ h.isFiniteLocallyFree
  infer_instance

/-- The actual polynomial-chart generators are the canonical ratio sections. -/
theorem ambientSectionsChartAlgEquiv_X {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    ambientSectionsChartAlgEquiv i (X j) = coordinateRatio i (i.succAbove j) := by
  have hX : Stacks.ProjectiveChart.chartRingEquiv ℂ i (X j) =
      Stacks.ProjectiveChart.ratio ℂ i (i.succAbove j) := by
    change Stacks.ProjectiveChart.chartHom ℂ i
      (MvPolynomial.map (Stacks.ProjectiveChart.degreeZeroEquiv ℂ n).symm.toRingHom (X j)) = _
    rw [MvPolynomial.map_X]
    exact MvPolynomial.aeval_X _ _
  change Stacks.ProjectiveChart.sectionsChartEquiv ℂ i (X j) = _
  rw [coordinateRatio, homogeneousSectionsEquiv_apply]
  change ((Proj.basicOpenIsoAway (homogeneousSubmodule (Fin (n+1)) ℂ) (X i)
    (Stacks.ProjectiveChart.X_mem_degree_one ℂ i) Nat.one_pos).hom).hom
      (Stacks.ProjectiveChart.chartRingEquiv ℂ i (X j)) = _
  rw [Proj.basicOpenIsoAway_hom, hX]

/-- Actual relative biderivations agreeing on coordinate-ratio pairs on every
standard chart agree on every section of every open. Quasicoherent affine
faithfulness is what propagates the source contraction to all subopens. -/
theorem projective_biderivation_ext_on_ratios (n : ℕ)
    (B D : StructureSheafBiderivation (ProjectiveAmbient n))
    (hB : B.IsRelative (CotangentCoordinates.ambientProjection n))
    (hD : D.IsRelative (CotangentCoordinates.ambientProjection n))
    (h : ∀ (i : Fin (n+1)) (j k : Fin n),
      B.bracket (coordinateOpen i) (coordinateRatio i (i.succAbove j))
          (coordinateRatio i (i.succAbove k)) =
        D.bracket (coordinateOpen i) (coordinateRatio i (i.succAbove j))
          (coordinateRatio i (i.succAbove k))) :
    ∀ (U : (ProjectiveAmbient n).Opens) (a b : Γ(ProjectiveAmbient n,U)),
      B.bracket U a b = D.bracket U a b := by
  let f := CotangentCoordinates.ambientProjection n
  let : (Scheme.Hom.relativeDifferentials f).IsQuasicoherent :=
    Scheme.Hom.isQuasicoherent_relativeDifferentials f
  let : (tangentSheaf f).IsQuasicoherent := projective_tangent_isQuasicoherent n
  apply relative_biderivation_ext_of_affine_cover f
    (fun i : Fin (n+1) => coordinateOpen i)
    (fun i => CotangentCoordinates.cotangentChartOpen_affine i)
    (Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top ℂ n) B D hB hD
  intro i
  apply biderivation_ext_on_polynomial_chart f B D hB hD (coordinateOpen i)
    (ambientSectionsChartAlgEquiv i)
  intro j k
  simpa only [ambientSectionsChartAlgEquiv_X] using h i j k
end Projective
end NcCubic.Geometry
