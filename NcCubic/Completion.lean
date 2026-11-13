module
public import NcCubic.Geometry.GeometricRepresentation
public import NcCubic.Geometry.GeometricCanonicalDirections
@[expose] public noncomputable section
namespace NcCubic
open Geometry

/-- The original algebraic geometric classification, for genuine nonzero
Poisson bivectors, together with its converse. -/
theorem theorem113 : Geometry.GeometricClassificationStatement := by
  intro n hN Y i _ _ F hF0 hF hideal
  constructor
  · intro pi hpi hJac
    obtain ⟨P,hRep⟩ := exists_standardRepresentative (by omega) i F hF0 hF hideal pi
    exact ⟨P, GeometricForward.blockNormalForm_of_standardRepresentative_canonical
      i hN F hF0 hF hideal pi hpi hJac P hRep, hRep⟩
  · intro P hNF
    exact GeometricConverse.exists_bivector_of_normalForm i hN F hF0 P hF hideal hNF
end NcCubic
