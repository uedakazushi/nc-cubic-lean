module
public import NcCubic.Geometry.AmbientProjectivePoisson
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

theorem ambientProjectiveBracket_basic
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial (n+1)} {d : ℕ} (hd : 0<d) (hh : h.IsHomogeneous d)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) :
    (ambientProjectiveBracket q hq).bracket _ a b = HomogeneousSections.bracket q hq hd hh a b := by
  let s : PositiveBasicIndex n := ⟨⟨d,hd⟩,⟨h,hh⟩⟩
  have ht := (ambientBasisBracket q hq).gluedBracket_restrict _ a b s le_rfl
  dsimp [s,positiveBasicOpen,ambientBasisBracket] at ht
  have hid : (homOfLE (le_refl (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h))).op =
      𝟙 (Opposite.op (Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) h)) := rfl
  rw [hid,CategoryTheory.Functor.map_id] at ht
  exact ht

theorem homogeneousSectionBracket_restrict_le
    (q : Fin (n+1) → Fin (n+1) → CubicPolynomial (n+1))
    (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {f g : CubicPolynomial (n+1)} {d e : ℕ}
    (hd : 0<d) (hf : f.IsHomogeneous d) (he : 0<e) (hg : g.IsHomogeneous e)
    (h : Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) g ≤
      Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) f)
    (a b : Γ(ProjectiveAmbient n,Proj.basicOpen (homogeneousSubmodule (Fin (n+1)) ℂ) f)) :
    ((ProjectiveAmbient n).presheaf.map (homOfLE h).op)
      (HomogeneousSections.bracket q hq hd hf a b) =
    HomogeneousSections.bracket q hq he hg
      (((ProjectiveAmbient n).presheaf.map (homOfLE h).op) a)
      (((ProjectiveAmbient n).presheaf.map (homOfLE h).op) b) := by
  rw [← ambientProjectiveBracket_basic q hq hd hf,
    (ambientProjectiveBracket q hq).restrict,ambientProjectiveBracket_basic q hq he hg]
end NcCubic.Geometry
