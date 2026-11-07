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
/-- Binary operations on a genuine basis of opens. Compatibility is stated on
actual intersections and arbitrary sections with equal restrictions. -/
structure BasisBracketData (X : Scheme.{u}) (W : ι → X.Opens) where
  cover (U : X.Opens) : U ≤ ⨆ i : {i // W i ≤ U}, W i.val
  bracket (i : ι) : Γ(X,W i) → Γ(X,W i) → Γ(X,W i)
  overlap (i j : ι) (a b : Γ(X,W i)) (c d : Γ(X,W j))
    (ha : (X.presheaf.map (homOfLE inf_le_left).op) a =
      (X.presheaf.map (homOfLE inf_le_right).op) c)
    (hb : (X.presheaf.map (homOfLE inf_le_left).op) b =
      (X.presheaf.map (homOfLE inf_le_right).op) d) :
    (X.presheaf.map (homOfLE inf_le_left).op) (bracket i a b) =
      (X.presheaf.map (homOfLE inf_le_right).op) (bracket j c d)
namespace BasisBracketData
variable {W : ι → X.Opens} (D : BasisBracketData X W)
private theorem res_comp {U V T : X.Opens} (h : T ≤ V) (k : V ≤ U) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE k).op) a) =
      (X.presheaf.map (homOfLE (h.trans k)).op) a := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem existsUnique_glued (U : X.Opens) (a b : Γ(X,U)) :
    ∃! c : Γ(X,U), ∀ i (hi : W i ≤ U),
      (X.presheaf.map (homOfLE hi).op) c = D.bracket i
        ((X.presheaf.map (homOfLE hi).op) a) ((X.presheaf.map (homOfLE hi).op) b) := by
  have hg := X.sheaf.existsUnique_gluing' (fun i : {i // W i ≤ U} => W i.val) U
    (fun i => homOfLE i.property) (D.cover U)
    (fun i => D.bracket i.val ((X.presheaf.map (homOfLE i.property).op) a)
      ((X.presheaf.map (homOfLE i.property).op) b))
  have hc : TopCat.Presheaf.IsCompatible X.presheaf (fun i : {i // W i ≤ U} => W i.val)
      (fun i => D.bracket i.val ((X.presheaf.map (homOfLE i.property).op) a)
        ((X.presheaf.map (homOfLE i.property).op) b)) := by
    intro i j
    apply D.overlap
    · simp only [res_comp]
    · simp only [res_comp]
  obtain ⟨c,hc,hu⟩ := hg hc
  refine ⟨c, ?_, ?_⟩
  · intro i hi
    exact hc ⟨i,hi⟩
  · intro d hd
    exact hu d (fun i => hd i.val i.property)

def gluedBracket (U : X.Opens) (a b : Γ(X,U)) : Γ(X,U) :=
  (D.existsUnique_glued U a b).exists.choose

theorem gluedBracket_restrict (U : X.Opens) (a b : Γ(X,U)) (i : ι) (hi : W i ≤ U) :
    (X.presheaf.map (homOfLE hi).op) (D.gluedBracket U a b) =
      D.bracket i ((X.presheaf.map (homOfLE hi).op) a) ((X.presheaf.map (homOfLE hi).op) b) :=
  (D.existsUnique_glued U a b).exists.choose_spec i hi

/-- The uniquely glued basis operation commutes with every open restriction. -/
def glued : StructureSheafBracket X where
  bracket := D.gluedBracket
  restrict {U V} h a b := by
    apply X.sheaf.eq_of_locally_eq' (fun i : {i // W i ≤ V} => W i.val) V
      (fun i => homOfLE i.property) (D.cover V)
    intro i
    change (X.presheaf.map (homOfLE i.property).op)
      ((X.presheaf.map (homOfLE h).op) (D.gluedBracket U a b)) =
      (X.presheaf.map (homOfLE i.property).op)
        (D.gluedBracket V ((X.presheaf.map (homOfLE h).op) a)
          ((X.presheaf.map (homOfLE h).op) b))
    rw [res_comp, D.gluedBracket_restrict, D.gluedBracket_restrict]
    simp only [res_comp]

include D in
/-- Equality of actual sections is detected on the supplied basis. -/
theorem eq_of_basis (U : X.Opens) (a b : Γ(X,U))
    (h : ∀ i (hi : W i ≤ U),
      (X.presheaf.map (homOfLE hi).op) a = (X.presheaf.map (homOfLE hi).op) b) : a = b := by
  apply X.sheaf.eq_of_locally_eq' (fun i : {i // W i ≤ U} => W i.val) U
    (fun i => homOfLE i.property) (D.cover U)
  intro i
  exact h i.val i.property

/-- A compatible operation on all opens is determined by its values on the basis. -/
theorem glued_unique (B : StructureSheafBracket X)
    (hB : ∀ i a b, B.bracket (W i) a b = D.bracket i a b)
    (U : X.Opens) (a b : Γ(X,U)) : B.bracket U a b = D.glued.bracket U a b := by
  apply D.eq_of_basis
  intro i hi
  change (X.presheaf.map (homOfLE hi).op) (B.bracket U a b) =
    (X.presheaf.map (homOfLE hi).op) (D.gluedBracket U a b)
  rw [B.restrict, D.gluedBracket_restrict]
  exact hB i _ _
end BasisBracketData

/-- Actual Poisson operations on a basis, with compatibility on intersections. -/
structure BasisPoissonData (X : Scheme.{u}) (W : ι → X.Opens)
    extends BasisBracketData X W where
  add_right (i) (a b c : Γ(X,W i)) : bracket i a (b+c) = bracket i a b + bracket i a c
  skew (i) (a b : Γ(X,W i)) : bracket i a b = -bracket i b a
  self_eq_zero (i) (a : Γ(X,W i)) : bracket i a a = 0
  leibniz (i) (a b c : Γ(X,W i)) : bracket i a (b*c) = b*bracket i a c + c*bracket i a b
  jacobi (i) (a b c : Γ(X,W i)) :
    bracket i a (bracket i b c) + bracket i b (bracket i c a) +
      bracket i c (bracket i a b) = 0

/-- Poisson brackets on a genuine basis glue on the full structure sheaf. -/
def BasisPoissonData.glued {W : ι → X.Opens} (D : BasisPoissonData X W) :
    StructureSheafPoisson X where
  toStructureSheafBracket := D.toBasisBracketData.glued
  add_right U a b c := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op)
      (D.toBasisBracketData.gluedBracket U a (b+c)) =
      (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a b + D.toBasisBracketData.gluedBracket U a c)
    simp only [map_add, BasisBracketData.gluedBracket_restrict]
    exact D.add_right i _ _ _
  skew U a b := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a b) =
      (X.presheaf.map (homOfLE hi).op) (-D.toBasisBracketData.gluedBracket U b a)
    simp only [map_neg, BasisBracketData.gluedBracket_restrict]
    exact D.skew i _ _
  self_eq_zero U a := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a a) =
      (X.presheaf.map (homOfLE hi).op) 0
    simp only [map_zero, BasisBracketData.gluedBracket_restrict]
    exact D.self_eq_zero i _
  leibniz U a b c := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op) (D.toBasisBracketData.gluedBracket U a (b*c)) =
      (X.presheaf.map (homOfLE hi).op) (b*D.toBasisBracketData.gluedBracket U a c + c*D.toBasisBracketData.gluedBracket U a b)
    simp only [map_add, map_mul, BasisBracketData.gluedBracket_restrict]
    exact D.leibniz i _ _ _
  jacobi U a b c := by
    apply D.toBasisBracketData.eq_of_basis
    intro i hi
    change (X.presheaf.map (homOfLE hi).op)
      (D.toBasisBracketData.gluedBracket U a (D.toBasisBracketData.gluedBracket U b c) +
        D.toBasisBracketData.gluedBracket U b (D.toBasisBracketData.gluedBracket U c a) +
        D.toBasisBracketData.gluedBracket U c (D.toBasisBracketData.gluedBracket U a b)) =
      (X.presheaf.map (homOfLE hi).op) 0
    simp only [map_add, map_zero, BasisBracketData.gluedBracket_restrict]
    exact D.jacobi i _ _ _

/-- The full structure-sheaf bracket restricts to the original basis bracket. -/
theorem BasisPoissonData.glued_restrict {W : ι → X.Opens} (D : BasisPoissonData X W)
    (U : X.Opens) (a b : Γ(X,U)) (i : ι) (hi : W i ≤ U) :
    (X.presheaf.map (homOfLE hi).op) (D.glued.bracket U a b) =
      D.bracket i ((X.presheaf.map (homOfLE hi).op) a) ((X.presheaf.map (homOfLE hi).op) b) :=
  D.toBasisBracketData.gluedBracket_restrict U a b i hi
end NcCubic.Geometry
