module
public import NcCubic.Geometry.BivectorContractionNaturality
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false in
def siteSectionEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M).obj (op U) ≃ₗ[Γ(X,U)]
      Γ(M,U) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency false in
def exteriorContractionLinear {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) :
    (⋀[Γ(X,U)]^2
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (tangentSheaf f)).obj (op U)))
    →ₗ[Γ(X,U)]
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (tangentContractionSheaf f)).obj (op U) :=
  (siteSectionEquiv (tangentContractionSheaf f) U).symm.toLinearMap.comp
    ((exteriorPower.alternatingMapLinearEquiv (wedgeContractionAlternating f U)).comp
      (exteriorPower.map (R := Γ(X,U)) 2 (siteSectionEquiv (tangentSheaf f) U).toLinearMap))

set_option backward.isDefEq.respectTransparency false in
theorem exteriorContractionLinear_ιMulti {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (tangentSheaf f)).obj (op U)) :
    exteriorContractionLinear f U (exteriorPower.ιMulti Γ(X,U) 2 v) =
      (siteSectionEquiv (tangentContractionSheaf f) U).symm
        (wedgeContractionLocal f U (fun i => siteSectionEquiv (tangentSheaf f) U (v i))) := by
  simp only [exteriorContractionLinear, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

def siteRingEquiv (X : Scheme.{u}) (U : X.Opens) :
    (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U) ≃+* Γ(X,U) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
instance siteRingEquiv_invPair (X : Scheme.{u}) (U : X.Opens) :
    RingHomInvPair (RingHomClass.toRingHom (siteRingEquiv X U))
      (RingHomClass.toRingHom (siteRingEquiv X U).symm) where
  comp_eq := by ext x; rfl
  comp_eq₂ := by ext x; rfl
instance siteRingEquiv_invPair_symm (X : Scheme.{u}) (U : X.Opens) :
    RingHomInvPair (RingHomClass.toRingHom (siteRingEquiv X U).symm)
      (RingHomClass.toRingHom (siteRingEquiv X U)) where
  comp_eq := by ext x; rfl
  comp_eq₂ := by ext x; rfl
set_option backward.isDefEq.respectTransparency false in
def siteSectionSemilinearEquiv {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    LinearEquiv (RingHomClass.toRingHom (siteRingEquiv X U))
      (σ' := RingHomClass.toRingHom (siteRingEquiv X U).symm)
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M).obj (op U)) Γ(M,U) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
set_option backward.isDefEq.respectTransparency false in
def exteriorContractionRawLinear {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) :
    (⋀[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]^2
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (tangentSheaf f)).obj (op U)))
    →ₗ[(X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)]
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (tangentContractionSheaf f)).obj (op U) where
  toFun x := (siteSectionSemilinearEquiv (tangentContractionSheaf f) U).symm
    (exteriorPower.alternatingMapLinearEquiv (wedgeContractionAlternating f U)
      (ExteriorAlgebra.powMapₛₗ 2 (RingHomClass.toRingHom (siteRingEquiv X U))
        (siteSectionSemilinearEquiv (tangentSheaf f) U).toLinearMap x))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    simp only [map_smulₛₗ]
    rfl
set_option backward.isDefEq.respectTransparency false in
theorem exteriorContractionRawLinear_ιMulti {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (tangentSheaf f)).obj (op U)) :
    exteriorContractionRawLinear f U
      (exteriorPower.ιMulti ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U)) 2 v) =
      (siteSectionSemilinearEquiv (tangentContractionSheaf f) U).symm
        (wedgeContractionLocal f U (fun i => siteSectionSemilinearEquiv (tangentSheaf f) U (v i))) := by
  change (siteSectionSemilinearEquiv (tangentContractionSheaf f) U).symm
    (exteriorPower.alternatingMapLinearEquiv (wedgeContractionAlternating f U)
      (ExteriorAlgebra.powMapₛₗ 2 (RingHomClass.toRingHom (siteRingEquiv X U))
        (siteSectionSemilinearEquiv (tangentSheaf f) U).toLinearMap _)) = _
  rw [ExteriorAlgebra.powMapₛₗ_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl
section Generic
variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable {σ : R →+* S} {τ : S →+* R} [RingHomInvPair σ τ]
variable {M N M' N' ι : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid M'] [AddCommMonoid N']
variable [Module R M] [Module R N] [Module S M'] [Module S N']
def alternatingSemilinearTransport (A : AlternatingMap S M' N' ι)
    (f : M →ₛₗ[σ] M') (g : N' →ₛₗ[τ] N) : AlternatingMap R M N ι where
  toFun v := g (A (f ∘ v))
  map_update_add' v i x y := by
    simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
  map_update_smul' v i c x := by
    simp only [Function.comp_update, map_smulₛₗ, AlternatingMap.map_update_smul,
      RingHomInvPair.comp_apply_eq]
  map_eq_zero_of_eq' v i j hij hne := by
    rw [A.map_eq_zero_of_eq (f ∘ v) (congrArg f hij) hne, map_zero]
end Generic
set_option backward.isDefEq.respectTransparency false in
def wedgeContractionRawAlternating {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) :
    AlternatingMap ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (op U))
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) (tangentSheaf f)).obj (op U))
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (tangentContractionSheaf f)).obj (op U)) (Fin 2) :=
  alternatingSemilinearTransport (wedgeContractionAlternating f U)
    (siteSectionSemilinearEquiv (tangentSheaf f) U).toLinearMap
    (siteSectionSemilinearEquiv (tangentContractionSheaf f) U).symm.toLinearMap
set_option backward.isDefEq.respectTransparency false in
theorem siteSectionSemilinearEquiv_natural {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (h : V ⟶ U)
    (x : (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M).obj (op U)) :
    siteSectionSemilinearEquiv M V
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) M).map h.op x) =
      M.presheaf.map h.op (siteSectionSemilinearEquiv M U x) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem wedgeContractionRawAlternating_eval {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (tangentSheaf f)).obj (op U)) :
    siteSectionSemilinearEquiv (tangentContractionSheaf f) U
      (wedgeContractionRawAlternating f U v) =
      wedgeContractionLocal f U (fun i => siteSectionSemilinearEquiv (tangentSheaf f) U (v i)) := by
  exact (siteSectionSemilinearEquiv (tangentContractionSheaf f) U).apply_symm_apply _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
theorem wedgeContractionRawAlternating_natural {X S : Scheme.{u}} (f : X ⟶ S)
    {U V : X.Opens} (h : V ⟶ U)
    (v : Fin 2 → (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (tangentSheaf f)).obj (op U)) :
    (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
      (tangentContractionSheaf f)).map h.op (wedgeContractionRawAlternating f U v) =
      wedgeContractionRawAlternating f V (fun i =>
        (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
          (tangentSheaf f)).map h.op (v i)) := by
  apply (siteSectionSemilinearEquiv (tangentContractionSheaf f) V).injective
  calc
    _ = (tangentContractionSheaf f).presheaf.map h.op
      (siteSectionSemilinearEquiv (tangentContractionSheaf f) U
        (wedgeContractionRawAlternating f U v)) :=
      siteSectionSemilinearEquiv_natural _ h _
    _ = (tangentContractionSheaf f).presheaf.map h.op
      (wedgeContractionLocal f U (fun i => siteSectionSemilinearEquiv (tangentSheaf f) U (v i))) :=
      congrArg _ (wedgeContractionRawAlternating_eval f U v)
    _ = wedgeContractionLocal f V (fun i => (tangentSheaf f).presheaf.map h.op
      (siteSectionSemilinearEquiv (tangentSheaf f) U (v i))) :=
      wedgeContractionLocal_restrict f h _
    _ = wedgeContractionLocal f V (fun i => siteSectionSemilinearEquiv (tangentSheaf f) V
      ((SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (tangentSheaf f)).map h.op (v i))) :=
      congrArg (wedgeContractionLocal f V)
        (funext fun i => (siteSectionSemilinearEquiv_natural (tangentSheaf f) h (v i)).symm)
    _ = _ := (wedgeContractionRawAlternating_eval f V _).symm
end NcCubic.Geometry
