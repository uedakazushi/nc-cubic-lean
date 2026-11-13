/- Exact every-open comparison of the positive Euler quadratic representative
with the actual ambient projective bracket. Canonical column compatibility
is explicit until the concrete Euler-map theorem is supplied. -/
module
public import NcCubic.Geometry.AlgebraicQuadraticBracket
public import NcCubic.Geometry.AmbientQuadraticRatioBracket
public import NcCubic.Geometry.ProjectiveBiderivationExt
public import NcCubic.Geometry.CanonicalImmersionBracket
public import NcCubic.Geometry.QuadraticRepresentative
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
open NcCubic.Geometry.CanonicalEulerCoordinateEvaluation NcCubic.Geometry.CoordinateTwistFrame
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option Elab.async false
namespace NcCubic.Geometry.QuadraticProjectiveComparison
variable {n : ℕ}
lemma restrictedRatio_self (i l : Fin (n+1)) :
    restrictedRatio i l (ProjectiveCoordinateDerivatives.coordinateOpen i) le_rfl =
      ProjectiveCoordinateDerivatives.coordinateRatio i l := by
  change (ProjectiveAmbient n).presheaf.map (𝟙 (op (ProjectiveCoordinateDerivatives.coordinateOpen i)))
    (ProjectiveCoordinateDerivatives.coordinateRatio i l) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

private lemma biderivation_at_eq {X : Scheme} (B : StructureSheafBiderivation X)
    (D : StructureSheafBracket X) (h : B.toStructureSheafBracket = D)
    (U : X.Opens) (a b : Γ(X,U)) : B.bracket U a b = D.bracket U a b :=
  congrArg (fun T : StructureSheafBracket X => T.bracket U a b) h

lemma quadratic_bracket_on_ratios_of_actions
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (CotangentCoordinates.ambientProjection n))
    (haction : HasCanonicalRatioAction g)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2))
    (i l m : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) :
    (algebraicBivectorBracket (X := CanonicalTwistDuality.projective ℂ n) (CotangentCoordinates.ambientProjection n)
      ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n) (n+1) g).val.app (op ⊤) σ)).bracket U
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
    (ambientProjectiveBracket (quadraticRepresentative n σ) (quadraticRepresentative_homogeneous n σ)).bracket U
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) := by
  have ha := algebraicQuadratic_ratio_bracket_of_actions (n := n) g haction σ i l m U hU
  have hb := AmbientQuadraticRatioBracket.ambient_pair_ratio_bracket (n := n)
    (fun (s : Set.powersetCard (Fin (n+1)) 2) j => Set.powersetCard.ofFinEmbEquiv.symm s j)
    (fun s => ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n (n+1) σ s) i l m U hU
  have hd := biderivation_at_eq
    (ambientProjectiveBiderivation (quadraticRepresentative n σ)
      (quadraticRepresentative_homogeneous n σ) (quadraticRepresentative_skew n σ))
    (ambientProjectiveBracket (quadraticRepresentative n σ) (quadraticRepresentative_homogeneous n σ))
    (ambientProjectiveBiderivation_toBracket _ _ _) U
    (restrictedRatio i l U hU) (restrictedRatio i m U hU)
  exact ha.trans (hb.symm.trans hd)

/-- The representative gives the actual every-open bracket, without a Jacobi
assumption. Column compatibility is the remaining explicit Euler-map input. -/
lemma quadratic_bracket_all_opens_of_actions
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (CotangentCoordinates.ambientProjection n))
    (haction : HasCanonicalRatioAction g)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 (n+1)) 2)) :
    ∀ (U : (ProjectiveAmbient n).Opens) (a b : Γ(ProjectiveAmbient n,U)),
      (algebraicBivectorBracket (X := CanonicalTwistDuality.projective ℂ n) (CotangentCoordinates.ambientProjection n)
        ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n) (n+1) g).val.app (op ⊤) σ)).bracket U a b =
      (ambientProjectiveBracket (quadraticRepresentative n σ) (quadraticRepresentative_homogeneous n σ)).bracket U a b := by
  let pi : AlgebraicBivector (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) :=
    (quadraticExteriorMap (CotangentCoordinates.ambientProjection n) (n+1) g).val.app (op ⊤) σ
  let B := algebraicBivectorBiderivation (X := CanonicalTwistDuality.projective ℂ n) (CotangentCoordinates.ambientProjection n) pi
  let D := ambientProjectiveBiderivation (quadraticRepresentative n σ)
    (quadraticRepresentative_homogeneous n σ) (quadraticRepresentative_skew n σ)
  have hB (U : (ProjectiveAmbient n).Opens) (a b : Γ(ProjectiveAmbient n,U)) :
      B.bracket U a b = (algebraicBivectorBracket (X := CanonicalTwistDuality.projective ℂ n)
        (CotangentCoordinates.ambientProjection n) pi).bracket U a b :=
    biderivation_at_eq B _ (algebraicBivectorBiderivation_toBracket _ _) U a b
  have hD (U : (ProjectiveAmbient n).Opens) (a b : Γ(ProjectiveAmbient n,U)) :
      D.bracket U a b = (ambientProjectiveBracket (quadraticRepresentative n σ)
        (quadraticRepresentative_homogeneous n σ)).bracket U a b :=
    biderivation_at_eq D _ (ambientProjectiveBiderivation_toBracket _ _ _) U a b
  have hR (i : Fin (n+1)) (j k : Fin n) :
      B.bracket (ProjectiveCoordinateDerivatives.coordinateOpen i)
        (ProjectiveCoordinateDerivatives.coordinateRatio i (i.succAbove j))
        (ProjectiveCoordinateDerivatives.coordinateRatio i (i.succAbove k)) =
      D.bracket (ProjectiveCoordinateDerivatives.coordinateOpen i)
        (ProjectiveCoordinateDerivatives.coordinateRatio i (i.succAbove j))
        (ProjectiveCoordinateDerivatives.coordinateRatio i (i.succAbove k)) := by
    let U := ProjectiveCoordinateDerivatives.coordinateOpen i
    let a := restrictedRatio i (i.succAbove j) U le_rfl
    let b := restrictedRatio i (i.succAbove k) U le_rfl
    have hBR := congrArg₂ (B.bracket U) (restrictedRatio_self i (i.succAbove j))
      (restrictedRatio_self i (i.succAbove k))
    have hDR := congrArg₂ (D.bracket U) (restrictedRatio_self i (i.succAbove j))
      (restrictedRatio_self i (i.succAbove k))
    have hf := quadratic_bracket_on_ratios_of_actions (n := n) g haction σ i (i.succAbove j) (i.succAbove k) U le_rfl
    exact hBR.symm.trans ((hB U a b).trans (hf.trans ((hD U a b).symm.trans hDR)))
  have hAll := projective_biderivation_ext_on_ratios n B D
    (algebraicBivectorBiderivation_isRelative (X := CanonicalTwistDuality.projective ℂ n) (CotangentCoordinates.ambientProjection n) pi)
    (ambientProjectiveBiderivation_relative _ _ _) hR
  intro U a b
  exact (hB U a b).symm.trans ((hAll U a b).trans (hD U a b))

end NcCubic.Geometry.QuadraticProjectiveComparison
