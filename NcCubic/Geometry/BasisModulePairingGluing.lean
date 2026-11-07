module
public import NcCubic.Geometry.BasisPoissonGluing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.FinCases
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} {ι : Type u}

/-- Bilinear pairings on an actual open basis, with compatibility on overlaps. -/
structure BasisModulePairingData (X : Scheme.{u}) (M : X.Modules) (W : ι → X.Opens) where
  cover (U : X.Opens) : U ≤ ⨆ i : {i // W i ≤ U}, W i.val
  pair (i : ι) : Γ(M,W i) →ₗ[Γ(X,W i)] Γ(M,W i) →ₗ[Γ(X,W i)] Γ(X,W i)
  overlap (i j : ι) (a b : Γ(M,W i)) (c d : Γ(M,W j))
    (ha : M.presheaf.map (homOfLE inf_le_left).op a = M.presheaf.map (homOfLE inf_le_right).op c)
    (hb : M.presheaf.map (homOfLE inf_le_left).op b = M.presheaf.map (homOfLE inf_le_right).op d) :
    (X.presheaf.map (homOfLE inf_le_left).op) (pair i a b) =
      (X.presheaf.map (homOfLE inf_le_right).op) (pair j c d)

namespace BasisModulePairingData
variable {M : X.Modules} {W : ι → X.Opens} (D : BasisModulePairingData X M W)
private theorem ring_res_comp {U V T : X.Opens} (h : T ≤ V) (k : V ≤ U) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE k).op) a) =
      (X.presheaf.map (homOfLE (h.trans k)).op) a := by
  rw [← ConcreteCategory.comp_apply,← X.presheaf.map_comp]
  rfl
private theorem module_res_comp {U V T : X.Opens} (h : T ≤ V) (k : V ≤ U) (a : Γ(M,U)) :
    M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE k).op a) =
      M.presheaf.map (homOfLE (h.trans k)).op a :=
by
  rw [← ConcreteCategory.comp_apply,← M.presheaf.map_comp]
  rfl
private theorem module_res_smul {U V : X.Opens} (h : V ≤ U) (r : Γ(X,U)) (a : Γ(M,U)) :
    M.presheaf.map (homOfLE h).op (r • a) =
      (X.presheaf.map (homOfLE h).op) r • M.presheaf.map (homOfLE h).op a :=
  M.map_smul (homOfLE h) r a

theorem existsUnique_glued (U : X.Opens) (a b : Γ(M,U)) :
    ∃! c : Γ(X,U), ∀ i (hi : W i ≤ U),
      (X.presheaf.map (homOfLE hi).op) c = D.pair i
        (M.presheaf.map (homOfLE hi).op a) (M.presheaf.map (homOfLE hi).op b) := by
  have hg := X.sheaf.existsUnique_gluing' (fun i : {i // W i ≤ U} => W i.val) U
    (fun i => homOfLE i.property) (D.cover U)
    (fun i => D.pair i.val (M.presheaf.map (homOfLE i.property).op a)
      (M.presheaf.map (homOfLE i.property).op b))
  have hc : TopCat.Presheaf.IsCompatible X.presheaf (fun i : {i // W i ≤ U} => W i.val)
      (fun i => D.pair i.val (M.presheaf.map (homOfLE i.property).op a)
        (M.presheaf.map (homOfLE i.property).op b)) := by
    intro i j
    apply D.overlap
    · simp only [module_res_comp]
    · simp only [module_res_comp]
  obtain ⟨c,hc,hu⟩ := hg hc
  exact ⟨c,fun i hi => hc ⟨i,hi⟩,fun d hd => hu d (fun i => hd i.val i.property)⟩

def gluedPair (U : X.Opens) (a b : Γ(M,U)) : Γ(X,U) :=
  (D.existsUnique_glued U a b).exists.choose

theorem gluedPair_restrict (U : X.Opens) (a b : Γ(M,U)) (i : ι) (hi : W i ≤ U) :
    (X.presheaf.map (homOfLE hi).op) (D.gluedPair U a b) =
      D.pair i (M.presheaf.map (homOfLE hi).op a) (M.presheaf.map (homOfLE hi).op b) :=
  (D.existsUnique_glued U a b).exists.choose_spec i hi

include D in
theorem eq_of_basis (U : X.Opens) (a b : Γ(X,U))
    (h : ∀ i (hi : W i ≤ U),(X.presheaf.map (homOfLE hi).op) a =
      (X.presheaf.map (homOfLE hi).op) b) : a=b := by
  apply X.sheaf.eq_of_locally_eq' (fun i : {i // W i ≤ U} => W i.val) U
    (fun i => homOfLE i.property) (D.cover U)
  intro i
  exact h i.val i.property

theorem gluedPair_natural {U V : X.Opens} (h : V ≤ U) (a b : Γ(M,U)) :
    (X.presheaf.map (homOfLE h).op) (D.gluedPair U a b) =
      D.gluedPair V (M.presheaf.map (homOfLE h).op a) (M.presheaf.map (homOfLE h).op b) := by
  apply D.eq_of_basis
  intro i hi
  rw [ring_res_comp,D.gluedPair_restrict,D.gluedPair_restrict]
  simp only [module_res_comp]

def gluedLinear (U : X.Opens) :
    Γ(M,U) →ₗ[Γ(X,U)] Γ(M,U) →ₗ[Γ(X,U)] Γ(X,U) where
  toFun a := {
    toFun := D.gluedPair U a
    map_add' b c := by
      apply D.eq_of_basis
      intro i hi
      simp only [map_add,D.gluedPair_restrict]
    map_smul' r b := by
      apply D.eq_of_basis
      intro i hi
      simp only [D.gluedPair_restrict,module_res_smul,map_smul,smul_eq_mul,map_mul,RingHom.id_apply]
      }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change D.gluedPair U (a+b) c = D.gluedPair U a c + D.gluedPair U b c
    apply D.eq_of_basis
    intro i hi
    simp only [LinearMap.add_apply,map_add,D.gluedPair_restrict]
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    change D.gluedPair U (r • a) b = r • D.gluedPair U a b
    apply D.eq_of_basis
    intro i hi
    simp only [LinearMap.smul_apply,D.gluedPair_restrict,module_res_smul,map_smul,smul_eq_mul,map_mul]

theorem gluedPair_self (hdiag : ∀ i (a : Γ(M,W i)),D.pair i a a=0)
    (U : X.Opens) (a : Γ(M,U)) : D.gluedPair U a a=0 := by
  apply D.eq_of_basis
  intro i hi
  rw [D.gluedPair_restrict,map_zero,hdiag]

def gluedAlternating (hdiag : ∀ i (a : Γ(M,W i)),D.pair i a a=0) (U : X.Opens) :
    AlternatingMap Γ(X,U) Γ(M,U) Γ(X,U) (Fin 2) where
  toFun v := D.gluedLinear U (v 0) (v 1)
  map_update_add' v i a b := by fin_cases i <;> simp
  map_update_smul' v i r a := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0=v 1 at hij
      rw [hij]
      exact D.gluedPair_self hdiag U _
    · change v 1=v 0 at hij
      rw [← hij]
      exact D.gluedPair_self hdiag U _
    · exact (hne rfl).elim

theorem gluedAlternating_natural (hdiag : ∀ i (a : Γ(M,W i)),D.pair i a a=0)
    {U V : X.Opens} (h : V≤U) (v : Fin 2 → Γ(M,U)) :
    (X.presheaf.map (homOfLE h).op) (D.gluedAlternating hdiag U v) =
      D.gluedAlternating hdiag V (fun i => M.presheaf.map (homOfLE h).op (v i)) :=
  D.gluedPair_natural h (v 0) (v 1)
end BasisModulePairingData
end NcCubic.Geometry
