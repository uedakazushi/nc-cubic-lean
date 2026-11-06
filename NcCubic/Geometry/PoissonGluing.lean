/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.PoissonSheaf
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {ι : Type u}
/-- Brackets on subopens of each covering open, with honest overlap equality. -/
structure LocalBracketData (X : Scheme.{u}) (W : ι → X.Opens) where
  bracket (i : ι) (U : X.Opens) : Γ(X,U) → Γ(X,U) → Γ(X,U)
  restrict (i) {U V : X.Opens} (hU : U ≤ W i) (h : V ≤ U) (a b : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) (bracket i U a b) =
      bracket i V ((X.presheaf.map (homOfLE h).op) a)
        ((X.presheaf.map (homOfLE h).op) b)
  agree (i j) (U : X.Opens) (hi : U ≤ W i) (hj : U ≤ W j) (a b : Γ(X,U)) :
    bracket i U a b = bracket j U a b
namespace LocalBracketData
variable {W : ι → X.Opens} (D : LocalBracketData X W)
private theorem restriction_comp {U V T : X.Opens} (h : T ≤ V) (k : V ≤ U)
    (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE k).op) a) =
      (X.presheaf.map (homOfLE (h.trans k)).op) a := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem existsUnique_glued (hW : iSup W = ⊤) (U : X.Opens) (a b : Γ(X,U)) :
    ∃! c : Γ(X,U), ∀ i,
      (X.presheaf.map (homOfLE (show U ⊓ W i ≤ U from inf_le_left)).op) c =
        D.bracket i (U ⊓ W i)
          ((X.presheaf.map (homOfLE inf_le_left).op) a)
          ((X.presheaf.map (homOfLE inf_le_left).op) b) := by
  apply X.sheaf.existsUnique_gluing' (fun i => U ⊓ W i) U
    (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hW])
  intro i j
  change (X.presheaf.map (homOfLE inf_le_left).op) (D.bracket i _ _ _) =
    (X.presheaf.map (homOfLE inf_le_right).op) (D.bracket j _ _ _)
  rw [D.restrict i inf_le_right, D.restrict j inf_le_right]
  simp only [restriction_comp]
  exact D.agree i j _ (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) _ _

/-- The uniquely glued operation on the actual section ring. -/
def gluedBracket (hW : iSup W = ⊤) (U : X.Opens) (a b : Γ(X,U)) : Γ(X,U) :=
  (D.existsUnique_glued hW U a b).exists.choose

theorem gluedBracket_restrict (hW : iSup W = ⊤) (U : X.Opens) (a b : Γ(X,U)) (i : ι) :
    (X.presheaf.map (homOfLE (show U ⊓ W i ≤ U from inf_le_left)).op)
      (D.gluedBracket hW U a b) =
    D.bracket i (U ⊓ W i) ((X.presheaf.map (homOfLE inf_le_left).op) a)
      ((X.presheaf.map (homOfLE inf_le_left).op) b) :=
  (D.existsUnique_glued hW U a b).exists.choose_spec i

/-- The glued operation commutes with every restriction, rather than only
restrictions appearing in the original cover. -/
def glued (hW : iSup W = ⊤) : StructureSheafBracket X where
  bracket := D.gluedBracket hW
  restrict {U V} h a b := by
    apply X.sheaf.eq_of_locally_eq' (fun i => V ⊓ W i) V
      (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hW])
    intro i
    change (X.presheaf.map (homOfLE inf_le_left).op)
      ((X.presheaf.map (homOfLE h).op) (D.gluedBracket hW U a b)) =
      (X.presheaf.map (homOfLE inf_le_left).op)
        (D.gluedBracket hW V ((X.presheaf.map (homOfLE h).op) a)
          ((X.presheaf.map (homOfLE h).op) b))
    rw [D.gluedBracket_restrict]
    have hv : V ⊓ W i ≤ U ⊓ W i := inf_le_inf h le_rfl
    have hc := congrArg (fun t => (X.presheaf.map (homOfLE hv).op) t)
      (D.gluedBracket_restrict hW U a b i)
    rw [D.restrict i inf_le_right hv] at hc
    simp only [restriction_comp] at hc ⊢
    exact hc

/-- On every subopen of a chart, the global operation is the original one. -/
theorem glued_eq_of_le (hW : iSup W = ⊤) (i : ι) (U : X.Opens) (hU : U ≤ W i)
    (a b : Γ(X,U)) : (D.glued hW).bracket U a b = D.bracket i U a b := by
  apply X.sheaf.eq_of_locally_eq' (fun j => U ⊓ W j) U
    (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hW])
  intro j
  change (X.presheaf.map (homOfLE inf_le_left).op) (D.gluedBracket hW U a b) =
    (X.presheaf.map (homOfLE inf_le_left).op) (D.bracket i U a b)
  rw [D.gluedBracket_restrict, D.restrict i hU]
  exact D.agree j i _ inf_le_right (inf_le_left.trans hU) _ _

/-- Equality on the cover determines the glued operation uniquely. -/
theorem glued_unique (hW : iSup W = ⊤) (B : StructureSheafBracket X)
    (hB : ∀ i U, U ≤ W i → ∀ a b, B.bracket U a b = D.bracket i U a b)
    (U : X.Opens) (a b : Γ(X,U)) :
    B.bracket U a b = (D.glued hW).bracket U a b := by
  apply X.sheaf.eq_of_locally_eq' (fun i => U ⊓ W i) U
    (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hW])
  intro i
  change (X.presheaf.map (homOfLE inf_le_left).op) (B.bracket U a b) =
    (X.presheaf.map (homOfLE inf_le_left).op) (D.gluedBracket hW U a b)
  rw [B.restrict, D.gluedBracket_restrict]
  exact hB i _ inf_le_right _ _
end LocalBracketData

/-- Poisson brackets on subopens of a cover, satisfying actual overlap equality. -/
structure LocalPoissonData (X : Scheme.{u}) (W : ι → X.Opens)
    extends LocalBracketData X W where
  add_right (i U) (hU : U ≤ W i) (a b c : Γ(X,U)) :
    bracket i U a (b+c) = bracket i U a b + bracket i U a c
  skew (i U) (hU : U ≤ W i) (a b : Γ(X,U)) : bracket i U a b = -bracket i U b a
  self_eq_zero (i U) (hU : U ≤ W i) (a : Γ(X,U)) : bracket i U a a = 0
  leibniz (i U) (hU : U ≤ W i) (a b c : Γ(X,U)) :
    bracket i U a (b*c) = b*bracket i U a c + c*bracket i U a b
  jacobi (i U) (hU : U ≤ W i) (a b c : Γ(X,U)) :
    bracket i U a (bracket i U b c) + bracket i U b (bracket i U c a) +
      bracket i U c (bracket i U a b) = 0

/-- Compatible chartwise Poisson brackets glue on the genuine structure sheaf. -/
def LocalPoissonData.glued {W : ι → X.Opens} (D : LocalPoissonData X W)
    (hW : iSup W = ⊤) : StructureSheafPoisson X := by
  apply (D.toLocalBracketData.glued hW).poissonOfCover W hW
  intro i U hU
  unfold StructureSheafBracket.IsPoissonOn
  simp_rw [D.toLocalBracketData.glued_eq_of_le hW i U hU]
  exact ⟨D.add_right i U hU, D.skew i U hU, D.self_eq_zero i U hU, D.leibniz i U hU, D.jacobi i U hU⟩

/-- Relative brackets remain relative after gluing: base functions are pulled
back by the actual scheme morphism, then tested locally. -/
theorem LocalPoissonData.glued_relative {R : Type u} [CommRing R]
    {W : ι → X.Opens} (D : LocalPoissonData X W) (hW : iSup W = ⊤)
    (f : X ⟶ Spec (CommRingCat.of R))
    (hR : ∀ i U, U ≤ W i → ∀ a r,
      D.bracket i U a (AffineSmoothness.coefficientMap f U r) = 0) :
    (D.glued hW).IsRelative f := by
  intro U a r
  apply X.sheaf.eq_of_locally_eq' (fun i => U ⊓ W i) U
    (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hW])
  intro i
  change (X.presheaf.map (homOfLE inf_le_left).op)
    ((D.toLocalBracketData.glued hW).bracket U a
      (AffineSmoothness.coefficientMap f U r)) =
    (X.presheaf.map (homOfLE inf_le_left).op) 0
  rw [(D.toLocalBracketData.glued hW).restrict, map_zero,
    D.toLocalBracketData.glued_eq_of_le hW i _ inf_le_right]
  have hc : (X.presheaf.map (homOfLE (show U ⊓ W i ≤ U from inf_le_left)).op)
      (AffineSmoothness.coefficientMap f U r) =
      AffineSmoothness.coefficientMap f (U ⊓ W i) r := by
    unfold AffineSmoothness.coefficientMap
    simp only [RingHom.comp_apply]
    have h := f.appLE_map (U := ⊤) (V := U) (V' := U ⊓ W i) le_top
      (homOfLE inf_le_left).op
    exact congrArg (fun g => g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  rw [hc]
  exact hR i _ inf_le_right _ r
end NcCubic.Geometry
