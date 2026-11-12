module
public import NcCubic.Geometry.EulerTangency
public import NcCubic.Geometry.PolynomialRepresentation
public import NcCubic.Geometry.ProjectiveRepresentative
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000
variable {n : ℕ}
/-- The explicit tangency divisibility produces a constant trivector with the
same actual bracket on every projective open. The divisibility is visible. -/
theorem exists_constantRepresentative_of_tangency
    (F : CubicPolynomial (n+1)) (hF0 : F ≠ 0) (hF : F.IsHomogeneous 3)
    (hgrad : HasIsolatedGradientZero F)
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hs : ∀ i j, q j i = -q i j) (hd : ∀ i j, (q i j).IsHomogeneous 2)
    (hdiv : ∀ i j, F ∣ eulerWedge1 (gradientContract2 F q) i j) :
    ∃ P : Trivector (n+1), ∀ (U : (ProjectiveAmbient n).Opens) (a b : Γ(ProjectiveAmbient n,U)),
      (ambientProjectiveBracket (contractionCoefficients F P)
        (contractionCoefficients_isHomogeneous F P hF)).bracket U a b =
      (ambientProjectiveBracket q hd).bracket U a b := by
  obtain ⟨A,hA,hhor,hdeg,hskew⟩ := horizontal_of_euler_coefficients_divisible
    (by omega : 0 < n+1) F hF0 hF q hs hd hdiv
  obtain ⟨P,hP,hunique⟩ := horizontal_quadratic_representation F hF hgrad
    (fun i j => q i j-(1/3:ℂ) • eulerWedge1 A i j) hskew hdeg hhor
  refine ⟨P, ?_⟩
  apply ambientProjectiveBracket_eq_of_eulerWedge q (contractionCoefficients F P) hd
    (contractionCoefficients_isHomogeneous F P hF) (fun i => -C (1/3:ℂ) * A i)
  intro i j
  rw [hP]
  simp only [eulerWedge1, smul_eq_C_mul]
  ring
end NcCubic.Geometry
