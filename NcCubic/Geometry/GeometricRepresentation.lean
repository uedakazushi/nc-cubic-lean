/- Actual every-open constant-trivector representation of every genuine
bivector on a smooth projective cubic. -/
module
public import NcCubic.Geometry.GeometricRepresentationCore
public import NcCubic.Geometry.CanonicalDataRatioAction
public import NcCubic.Geometry.ProjectiveAmbientReindex
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every genuine bivector on a smooth cubic admits its actual standard
constant-trivector representative, without any representation hypothesis. -/
theorem exists_standardRepresentative {n : ℕ} {Y : Scheme}
    (hn : 3 ≤ n) (i : Y ⟶ ProjectiveAmbient n) [IsClosedImmersion i]
    [Smooth (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)]
    (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hideal : ProjectiveSpectrum.Proj.idealOfClosedSubscheme
      (MvPolynomial.homogeneousSubmodule (Fin (n+1)) ℂ) i = Ideal.span {F})
    (pi : AlgebraicBivector (i ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff ℂ n)) :
    ∃ P : Trivector (n+1), HasStandardRepresentative i F hF hideal pi P := by
  apply ProjectiveAmbientReindex.exists_standardRepresentative_of_raw_brackets i F hF hideal pi
  exact exists_standardBracket_of_euler_actions_raw hn
    (CanonicalEulerMiddle.positiveEulerMiddleLiteralData ℂ n).iso
    (CanonicalEulerMiddle.literalData_hasCanonicalRatioAction n)
    (ProjectiveAmbientReindex.rawImmersion i) F hF0 hF
    (ChartComparison.isolated_gradient_of_scheme_smooth i F hF hF0 hideal) hideal
    (ProjectiveAmbientReindex.toRawBivector i (toNativeBivector i pi))
end NcCubic.Geometry
