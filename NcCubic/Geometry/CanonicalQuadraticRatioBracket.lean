module
public import NcCubic.Geometry.ProjectiveCotangentRank
public import NcCubic.Geometry.QuadraticBracketReconstruction
public import NcCubic.Geometry.CanonicalEulerCoordinateEvaluation
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjTwistRank
open CanonicalEulerCoordinateEvaluation CoordinateTwistFrame
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Sheaf CategoryTheory.sheafCompose
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
universe u
local instance (X : Scheme.{u}) : CategoryTheory.Limits.HasFiniteBiproducts X.Modules :=
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts
theorem nativeFrameColumn_comp_app {X : Scheme.{u}} (L T : X.Modules) (N : ℕ)
    (g : SheafExteriorFrame.sum (X := X) L N ⟶ T) (j : Fin N) (U : X.Opens) (v : Γ(L,U)) :
    g.val.app (op U) ((nativeFrameColumn (X := X) L N j).val.app (op U) v) =
      (nativeFrameColumn (X := X) L N j ≫ g).val.app (op U) v := rfl
variable {n : ℕ}
def chartFieldValue (i j l : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) : Γ(ProjectiveAmbient n,U) :=
  (if j=l then 1 else 0) - restrictedRatio i l U hU * (if j=i then 1 else 0)
/-- The actual positive Euler columns act on each affine coordinate ratio. -/
def HasCanonicalRatioAction
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n)) : Prop :=
  ∀ (i j l : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i),
    tangentSectionDerivation (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      (g.val.app (op U) ((nativeFrameColumn (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) j).val.app (op U)
        (frameOne i U hU))) (restrictedRatio i l U hU) = chartFieldValue i j l U hU

theorem canonicalFrameColumn_action
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n))
    (hc : ∀ j : Fin (n+1), nativeFrameColumn (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) j ≫ g = canonicalEulerField ℂ n j)
    (i j l : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) :
    tangentSectionDerivation (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      (g.val.app (op U) ((nativeFrameColumn (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) j).val.app (op U)
        (frameOne i U hU))) (restrictedRatio i l U hU) = chartFieldValue i j l U hU := by
  have he := nativeFrameColumn_comp_app (X := CanonicalTwistDuality.projective ℂ n)
    (twistObj ℂ n 1) _ (n+1) g j U (frameOne i U hU)
  have ha := congrArg (fun v : Γ(tangentSheaf (X := CanonicalTwistDuality.projective ℂ n)
      (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n), U) =>
    tangentSectionDerivation (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ))
      (CotangentCoordinates.ambientProjection n) U v (restrictedRatio i l U hU)) he
  have hb := congrArg (fun h : twistObj ℂ n 1 ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n)
      (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) =>
    tangentSectionDerivation (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ))
      (CotangentCoordinates.ambientProjection n) U (h.val.app (op U) (frameOne i U hU))
        (restrictedRatio i l U hU)) (hc j)
  exact ha.trans (hb.trans (canonicalEulerField_frame_ratio i l j U hU))

theorem quadraticComponent_ratio_bracket_of_actions
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n))
    (haction : HasCanonicalRatioAction g)
    (s : Set.powersetCard (Fin (n+1)) 2)
    (c : MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i l m : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) :
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n) (n+1) g).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticComponent ℂ n (n+1) s).val.app (op U)
          (ProjectiveCoordinateDerivatives.restrictedDegreeSection 2 c U)))
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
    let j := Set.powersetCard.ofFinEmbEquiv.symm s 0
    let k := Set.powersetCard.ofFinEmbEquiv.symm s 1
    QuadraticCoefficientRatio.ratioQuadratic c i U hU *
      (chartFieldValue i j l U hU * chartFieldValue i k m U hU -
        chartFieldValue i k l U hU * chartFieldValue i j m U hU) := by
  rw [quadraticComponent_coefficient_bracket (CotangentCoordinates.ambientProjection n) (n+1) s g c i U hU,
    quadraticComponent_frameTwo_bracket (CotangentCoordinates.ambientProjection n) (n+1) s g i U hU]
  dsimp only
  change _ * (_ * _ - _ * _) = _
  have hv (j t : Fin (n+1)) := haction i j t U hU
  simp only [hv]

theorem quadraticComponent_ratio_bracket
    (g : SheafExteriorFrame.sum (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) ⟶ tangentSheaf (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n))
    (hc : ∀ j : Fin (n+1), nativeFrameColumn (X := CanonicalTwistDuality.projective ℂ n) (twistObj ℂ n 1) (n+1) j ≫ g = canonicalEulerField ℂ n j)
    (s : Set.powersetCard (Fin (n+1)) 2)
    (c : MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ 2)
    (i l m : Fin (n+1)) (U : (ProjectiveAmbient n).Opens)
    (hU : U ≤ ProjectiveCoordinateDerivatives.coordinateOpen i) :
    bivectorSectionBracket (X := CanonicalTwistDuality.projective ℂ n) (S := Spec (CommRingCat.of ℂ)) (CotangentCoordinates.ambientProjection n) U
      ((quadraticExteriorMap (CotangentCoordinates.ambientProjection n) (n+1) g).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticComponent ℂ n (n+1) s).val.app (op U)
          (ProjectiveCoordinateDerivatives.restrictedDegreeSection 2 c U)))
        (restrictedRatio i l U hU) (restrictedRatio i m U hU) =
    let j := Set.powersetCard.ofFinEmbEquiv.symm s 0
    let k := Set.powersetCard.ofFinEmbEquiv.symm s 1
    QuadraticCoefficientRatio.ratioQuadratic c i U hU *
      (chartFieldValue i j l U hU * chartFieldValue i k m U hU -
        chartFieldValue i k l U hU * chartFieldValue i j m U hU) := by
  exact quadraticComponent_ratio_bracket_of_actions g (canonicalFrameColumn_action g hc) s c i l m U hU
end NcCubic.Geometry
