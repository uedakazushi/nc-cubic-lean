/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses. -/
module
public import NcCubic.Geometry.AffineSmoothness
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.RingTheory.Derivation.Basic
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
universe u
/-- A Poisson operation on the actual structure sheaf, including compatibility
with every restriction map. Scalar compatibility is imposed separately for a
specified structure morphism. -/
structure StructureSheafBracket (X : Scheme.{u}) where
  bracket (U : X.Opens) : Γ(X,U) → Γ(X,U) → Γ(X,U)
  restrict {U V : X.Opens} (h : V ≤ U) (a b : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) (bracket U a b) =
      bracket V ((X.presheaf.map (homOfLE h).op) a)
        ((X.presheaf.map (homOfLE h).op) b)

/-- The ordinary Poisson identities hold on every actual section ring. -/
structure StructureSheafPoisson (X : Scheme.{u}) extends StructureSheafBracket X where
  add_right (U) (a b c : Γ(X,U)) : bracket U a (b+c) = bracket U a b + bracket U a c
  skew (U) (a b : Γ(X,U)) : bracket U a b = -bracket U b a
  self_eq_zero (U) (a : Γ(X,U)) : bracket U a a = 0
  leibniz (U) (a b c : Γ(X,U)) : bracket U a (b*c) = b*bracket U a c + c*bracket U a b
  jacobi (U) (a b c : Γ(X,U)) :
    bracket U a (bracket U b c) + bracket U b (bracket U c a) +
      bracket U c (bracket U a b) = 0

namespace StructureSheafPoisson
variable {X : Scheme.{u}} (B : StructureSheafPoisson X)
theorem add_left (U) (a b c : Γ(X,U)) :
    B.bracket U (a+b) c = B.bracket U a c + B.bracket U b c := by
  rw [B.skew, B.add_right, neg_add]
  rw [← B.skew U a c, ← B.skew U b c]
@[simp] theorem zero_right (U) (a : Γ(X,U)) : B.bracket U a 0 = 0 := by
  have h := B.add_right U a 0 0
  simpa using h
@[simp] theorem zero_left (U) (a : Γ(X,U)) : B.bracket U 0 a = 0 := by
  rw [B.skew, B.zero_right, neg_zero]
@[simp] theorem one_right (U) (a : Γ(X,U)) : B.bracket U a 1 = 0 := by
  have h := B.leibniz U a 1 1
  simpa using h
@[simp] theorem one_left (U) (a : Γ(X,U)) : B.bracket U 1 a = 0 := by
  rw [B.skew, B.one_right, neg_zero]
/-- For a scheme over Spec R, relative Poisson brackets annihilate the
actual pulled-back base constants. -/
def IsRelative {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ U a r, B.bracket U a (AffineSmoothness.coefficientMap f U r) = 0

/-- Every relative Hamiltonian is an actual R-derivation of the section ring. -/
def hamiltonian {R : Type u} [CommRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) (hR : B.IsRelative f)
    (U : X.Opens) (a : Γ(X,U)) :
    letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
    Derivation R Γ(X,U) Γ(X,U) := by
  letI : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  refine Derivation.mk'
    { toFun := B.bracket U a
      map_add' := B.add_right U a
      map_smul' := ?_ } ?_
  · intro r b
    change B.bracket U a (AffineSmoothness.coefficientMap f U r * b) =
      AffineSmoothness.coefficientMap f U r * B.bracket U a b
    rw [B.leibniz, hR, mul_zero, add_zero]
  · intro b c
    exact B.leibniz U a b c
end StructureSheafPoisson

namespace StructureSheafBracket
variable {X : Scheme.{u}} (B : StructureSheafBracket X)
/-- Jacobi is local on any genuine open cover of an open set. -/
theorem jacobi_of_cover {ι : Type u} (U : X.Opens) (V : ι → X.Opens)
    (hVU : ∀ i, V i ≤ U) (hcover : U ≤ iSup V)
    (hJ : ∀ i (a b c : Γ(X,V i)),
      B.bracket (V i) a (B.bracket (V i) b c) +
      B.bracket (V i) b (B.bracket (V i) c a) +
      B.bracket (V i) c (B.bracket (V i) a b) = 0)
    (a b c : Γ(X,U)) :
    B.bracket U a (B.bracket U b c) + B.bracket U b (B.bracket U c a) +
      B.bracket U c (B.bracket U a b) = 0 := by
  apply X.sheaf.eq_of_locally_eq' V U (fun i => homOfLE (hVU i)) hcover
  intro i
  change (X.presheaf.map (homOfLE (hVU i)).op)
    (B.bracket U a (B.bracket U b c) + B.bracket U b (B.bracket U c a) +
      B.bracket U c (B.bracket U a b)) =
    (X.presheaf.map (homOfLE (hVU i)).op) 0
  simp only [map_add, map_zero, B.restrict]
  exact hJ i _ _ _
/-- Local Poisson identities for a restriction-compatible operation. -/
def IsPoissonOn (U : X.Opens) : Prop :=
  (∀ a b c, B.bracket U a (b+c) = B.bracket U a b + B.bracket U a c) ∧
  (∀ a b, B.bracket U a b = -B.bracket U b a) ∧
  (∀ a, B.bracket U a a = 0) ∧
  (∀ a b c, B.bracket U a (b*c) = b*B.bracket U a c + c*B.bracket U a b) ∧
  (∀ a b c, B.bracket U a (B.bracket U b c) +
    B.bracket U b (B.bracket U c a) + B.bracket U c (B.bracket U a b) = 0)

/-- Poisson identities may be checked on all subopens of a covering family.
The operation and its restrictions are unchanged by this construction. -/
def poissonOfCover {ι : Type u} (W : ι → X.Opens) (hcover : iSup W = ⊤)
    (hlocal : ∀ i U, U ≤ W i → B.IsPoissonOn U) : StructureSheafPoisson X where
  toStructureSheafBracket := B
  add_right U a b c := by
    apply X.sheaf.eq_of_locally_eq' (fun i => U ⊓ W i) U
      (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hcover])
    intro i
    change (X.presheaf.map (homOfLE inf_le_left).op) (B.bracket U a (b+c)) =
      (X.presheaf.map (homOfLE inf_le_left).op) (B.bracket U a b + B.bracket U a c)
    simp only [map_add, B.restrict]
    exact (hlocal i _ inf_le_right).1 _ _ _
  skew U a b := by
    apply X.sheaf.eq_of_locally_eq' (fun i => U ⊓ W i) U
      (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hcover])
    intro i
    change (X.presheaf.map (homOfLE inf_le_left).op) (B.bracket U a b) =
      (X.presheaf.map (homOfLE inf_le_left).op) (-B.bracket U b a)
    simp only [map_neg, B.restrict]
    exact (hlocal i _ inf_le_right).2.1 _ _
  self_eq_zero U a := by
    apply X.sheaf.eq_of_locally_eq' (fun i => U ⊓ W i) U
      (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hcover])
    intro i
    change (X.presheaf.map (homOfLE inf_le_left).op) (B.bracket U a a) =
      (X.presheaf.map (homOfLE inf_le_left).op) 0
    simp only [map_zero, B.restrict]
    exact (hlocal i _ inf_le_right).2.2.1 _
  leibniz U a b c := by
    apply X.sheaf.eq_of_locally_eq' (fun i => U ⊓ W i) U
      (fun _ => homOfLE inf_le_left) (by simp [← inf_iSup_eq, hcover])
    intro i
    change (X.presheaf.map (homOfLE inf_le_left).op) (B.bracket U a (b*c)) =
      (X.presheaf.map (homOfLE inf_le_left).op) (b*B.bracket U a c + c*B.bracket U a b)
    simp only [map_add, map_mul, B.restrict]
    exact (hlocal i _ inf_le_right).2.2.2.1 _ _ _
  jacobi U a b c := B.jacobi_of_cover U (fun i => U ⊓ W i)
    (fun _ => inf_le_left) (by simp [← inf_iSup_eq, hcover])
    (fun i => (hlocal i _ inf_le_right).2.2.2.2) a b c

end StructureSheafBracket
end NcCubic.Geometry
