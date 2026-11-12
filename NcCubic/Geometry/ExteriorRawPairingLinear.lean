module
public import NcCubic.Geometry.ExteriorRawPairingCore
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
theorem dualDeterminantRawAlternating_smul_left {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (c : Γ(X,U)) (lam mu : Γ(dualSheaf M,U)) (Z : (Over U)ᵒᵖ) :
    dualDeterminantRawAlternating M (c • lam) mu Z =
      (sliceRingEquiv X U Z).symm (X.presheaf.map Z.unop.hom.op c) •
        dualDeterminantRawAlternating M lam mu Z := by
  apply AlternatingMap.ext
  intro v
  apply (sliceUnitEquiv X U Z).injective
  simp only [smul_apply, map_smulₛₗ, dualDeterminantRawAlternating_eval,
    dualDeterminantAlternating_eval, dualPairing_smul]
  simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  ring
set_option backward.isDefEq.respectTransparency false in
theorem dualDeterminantRawAlternating_smul_right {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (c : Γ(X,U)) (lam mu : Γ(dualSheaf M,U)) (Z : (Over U)ᵒᵖ) :
    dualDeterminantRawAlternating M lam (c • mu) Z =
      (sliceRingEquiv X U Z).symm (X.presheaf.map Z.unop.hom.op c) •
        dualDeterminantRawAlternating M lam mu Z := by
  apply AlternatingMap.ext
  intro v
  apply (sliceUnitEquiv X U Z).injective
  simp only [smul_apply, map_smulₛₗ, dualDeterminantRawAlternating_eval,
    dualDeterminantAlternating_eval, dualPairing_smul]
  simp only [RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  ring

namespace PresheafExterior
variable {C : Type u} [Category.{u} C] {O : Cᵒᵖ ⥤ CommRingCat.{u}}
  {F G : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)} {n : ℕ}
theorem desc_add
    (A B D : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i)))
    (hB : ∀ {U V} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (B U v) = B V (fun i => F.map h (v i)))
    (hD : ∀ {U V} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (D U v) = D V (fun i => F.map h (v i)))
    (heq : ∀ U, D U = A U + B U) : desc D hD = desc A hA + desc B hB := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change descSections D U (PresheafOfModules.extPowSections n F U z) =
    descSections A U (PresheafOfModules.extPowSections n F U z) +
      descSections B U (PresheafOfModules.extPowSections n F U z)
  simp only [descSections, heq, map_add, LinearMap.add_apply]

theorem desc_app_smul
    (A B : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i)))
    (hB : ∀ {U V} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (B U v) = B V (fun i => F.map h (v i)))
    (q : ∀ U, (O ⋙ forget₂ _ RingCat).obj U)
    (heq : ∀ U, A U = q U • B U)
    (U : Cᵒᵖ) (z : (PresheafOfModules.extPow (O:=O) n F).obj U) :
    (desc A hA).app U z = q U • (desc B hB).app U z := by
  simp only [desc_app, descSections, heq, map_smul, LinearMap.smul_apply]

theorem desc_zero
    (A : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i)))
    (heq : ∀ U, A U = 0) : desc A hA = 0 := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change descSections A U (PresheafOfModules.extPowSections n F U z) = 0
  simp only [descSections, heq, map_zero, LinearMap.zero_apply]

end PresheafExterior

set_option backward.isDefEq.respectTransparency false in
theorem overExteriorFunctional_add {C : Type u} [Category.{u} C]
    (O : Cᵒᵖ ⥤ CommRingCat.{u})
    (P Q : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)) (U : C) (n : ℕ)
    (d d' : PresheafOfModules.extPow (O := (Over.forget U).op ⋙ O) n
        ((restrFun O U).obj P) ⟶ (restrFun O U).obj Q) :
    overExteriorFunctional O P Q U n (d+d') =
      overExteriorFunctional O P Q U n d + overExteriorFunctional O P Q U n d' := by
  simp only [overExteriorFunctional, Preadditive.comp_add]

set_option backward.isDefEq.respectTransparency false in
theorem localDeterminantPresheaf_add_left {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam lam' mu : Γ(dualSheaf M,U)) :
    localDeterminantPresheaf M (lam+lam') mu =
      localDeterminantPresheaf M lam mu + localDeterminantPresheaf M lam' mu := by
  apply PresheafExterior.desc_add
  exact fun Z => dualDeterminantRawAlternating_add_left M lam lam' mu Z

set_option backward.isDefEq.respectTransparency false in
theorem localRawExteriorPairing_add_left {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam lam' mu : Γ(dualSheaf M,U)) :
    localRawExteriorPairing M (lam+lam') mu =
      localRawExteriorPairing M lam mu + localRawExteriorPairing M lam' mu := by
  simp only [localRawExteriorPairing, localDeterminantPresheaf_add_left,
    Preadditive.comp_add, Preadditive.add_comp, overExteriorFunctional_add]

set_option backward.isDefEq.respectTransparency false in
theorem localDeterminantPresheaf_add_right {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu mu' : Γ(dualSheaf M,U)) :
    localDeterminantPresheaf M lam (mu+mu') =
      localDeterminantPresheaf M lam mu + localDeterminantPresheaf M lam mu' := by
  apply PresheafExterior.desc_add
  exact fun Z => dualDeterminantRawAlternating_add_right M lam mu mu' Z

set_option backward.isDefEq.respectTransparency false in
theorem localRawExteriorPairing_add_right {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam mu mu' : Γ(dualSheaf M,U)) :
    localRawExteriorPairing M lam (mu+mu') =
      localRawExteriorPairing M lam mu + localRawExteriorPairing M lam mu' := by
  simp only [localRawExteriorPairing, localDeterminantPresheaf_add_right,
    Preadditive.comp_add, Preadditive.add_comp, overExteriorFunctional_add]

set_option backward.isDefEq.respectTransparency false in
theorem localDeterminantPresheaf_self {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam : Γ(dualSheaf M,U)) : localDeterminantPresheaf M lam lam = 0 := by
  apply PresheafExterior.desc_zero
  exact fun Z => dualDeterminantRawAlternating_self M lam Z

set_option backward.isDefEq.respectTransparency false in
theorem localRawExteriorPairing_self {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (lam : Γ(dualSheaf M,U)) : localRawExteriorPairing M lam lam = 0 := by
  simp only [localRawExteriorPairing, localDeterminantPresheaf_self,
    Limits.comp_zero, Limits.zero_comp, overExteriorFunctional]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 4000000 in
theorem localRawExteriorPairing_smul_left {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (c : Γ(X,U)) (lam mu : Γ(dualSheaf M,U)) :
    localRawExteriorPairing M (c • lam) mu = c • localRawExteriorPairing M lam mu := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (localDeterminantPresheaf M (c • lam) mu).app Z z =
    (sliceRingEquiv X U Z).symm (X.presheaf.map Z.unop.hom.op c) •
      (localDeterminantPresheaf M lam mu).app Z z
  exact PresheafExterior.desc_app_smul
    (fun W => dualDeterminantRawAlternating M (c • lam) mu W)
    (fun W => dualDeterminantRawAlternating M lam mu W)
    (fun k v => dualDeterminantRawAlternating_natural M (c • lam) mu k v)
    (fun k v => dualDeterminantRawAlternating_natural M lam mu k v)
    (fun W => (sliceRingEquiv X U W).symm (X.presheaf.map W.unop.hom.op c))
    (fun W => dualDeterminantRawAlternating_smul_left M c lam mu W) Z z

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 4000000 in
theorem localRawExteriorPairing_smul_right {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (c : Γ(X,U)) (lam mu : Γ(dualSheaf M,U)) :
    localRawExteriorPairing M lam (c • mu) = c • localRawExteriorPairing M lam mu := by
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (localDeterminantPresheaf M lam (c • mu)).app Z z =
    (sliceRingEquiv X U Z).symm (X.presheaf.map Z.unop.hom.op c) •
      (localDeterminantPresheaf M lam mu).app Z z
  exact PresheafExterior.desc_app_smul
    (fun W => dualDeterminantRawAlternating M lam (c • mu) W)
    (fun W => dualDeterminantRawAlternating M lam mu W)
    (fun k v => dualDeterminantRawAlternating_natural M lam (c • mu) k v)
    (fun k v => dualDeterminantRawAlternating_natural M lam mu k v)
    (fun W => (sliceRingEquiv X U W).symm (X.presheaf.map W.unop.hom.op c))
    (fun W => dualDeterminantRawAlternating_smul_right M c lam mu W) Z z

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 4000000 in
def localRawExteriorAlternating {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    AlternatingMap Γ(X,U) Γ(dualSheaf M,U) Γ(exteriorRawDualSheaf M,U) (Fin 2) where
  toFun v := localRawExteriorPairing M (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> norm_num only [Function.update_apply, Fin.ext_iff]
    · exact localRawExteriorPairing_add_left M x y (v 1)
    · exact localRawExteriorPairing_add_right M (v 0) x y
  map_update_smul' v i c x := by
    fin_cases i <;> norm_num only [Function.update_apply, Fin.ext_iff]
    · exact localRawExteriorPairing_smul_left M c x (v 1)
    · exact localRawExteriorPairing_smul_right M c (v 0) x
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij
      change localRawExteriorPairing M (v 0) (v 1) = 0
      rw [hij]
      exact localRawExteriorPairing_self M _
    · change v 1 = v 0 at hij
      change localRawExteriorPairing M (v 0) (v 1) = 0
      rw [hij]
      exact localRawExteriorPairing_self M _
    · exact (hne rfl).elim

end NcCubic.Geometry
