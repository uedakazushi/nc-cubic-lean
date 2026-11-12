/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.ExteriorNativeStalk
public import NcCubic.Geometry.StalkFiniteFamily
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
theorem stalkHom_native_germ {X : Scheme.{u}} {F G : X.Modules} (f : F ⟶ G)
    (x : X) (U : X.Opens) (hx : x ∈ U) (s : Γ(F,U)) :
    stalkHom f x (TopCat.Presheaf.germ F.presheaf U x hx s) =
      TopCat.Presheaf.germ G.presheaf U x hx (f.app U s) :=
  stalkHom_germAt f x U hx s

set_option backward.isDefEq.respectTransparency false in
theorem dualStalkEquiv_native_germ {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] (x : X) (U : X.Opens) (hx : x ∈ U)
    (s : Γ(dualSheaf F,U)) (v : Γ(F,U)) :
    dualStalkEquiv F x (TopCat.Presheaf.germ (dualSheaf F).presheaf U x hx s)
      (TopCat.Presheaf.germ F.presheaf U x hx v) =
      X.presheaf.germ U x hx (evalAt F s v) :=
  dualStalkEquiv_germ F x U hx s v

set_option backward.isDefEq.respectTransparency false in
/-- The scalar determinant formula for the actual exterior-dual morphism. -/
def HasExteriorDeterminantFormula {X : Scheme.{u}} (M : X.Modules)
    (phi : Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ) ⟶
      dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ))) : Prop :=
  ∀ (U : X.Opens) (lam : Fin 2 → Γ(dualSheaf M,U)) (v : Fin 2 → Γ(M,U)),
    evalAt (Scheme.Modules.exteriorPower M (2:ℤ))
      (phi.app U (exteriorWedgeAlternating (dualSheaf M) U lam))
      (exteriorWedgeAlternating M U v) =
    evalAt M (lam 0) (v 0) * evalAt M (lam 1) (v 1) -
      evalAt M (lam 1) (v 0) * evalAt M (lam 0) (v 1)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem exteriorDuality_stalk_wedges {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] [(Scheme.Modules.exteriorPower M (2:ℤ)).IsFinitePresentation]
    (phi : Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ) ⟶
      dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)))
    (hphi : HasExteriorDeterminantFormula M phi) (x : X)
    (lam : Fin 2 → (dualSheaf M).presheaf.stalk x) (v : Fin 2 → M.presheaf.stalk x) :
    dualStalkEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) x
      (stalkHom phi x ((schemeExteriorStalkEquiv (dualSheaf M) 2 x).symm
        (exteriorPower.ιMulti (X.presheaf.stalk x) 2 lam)))
      ((schemeExteriorStalkEquiv M 2 x).symm
        (exteriorPower.ιMulti (X.presheaf.stalk x) 2 v)) =
    Matrix.det (n := Fin 2) (Matrix.of (fun i j => dualStalkEquiv M x (lam j) (v i))) := by
  rcases exists_germ_family (dualSheaf M) x lam with ⟨U, hxU, lamU, hlam⟩
  rcases exists_germ_family_le M x U hxU v with ⟨V, hVU, hxV, vV, hv⟩
  let lamV : Fin 2 → Γ(dualSheaf M,V) :=
    fun i => (dualSheaf M).presheaf.map (homOfLE hVU).op (lamU i)
  have hlamV (i : Fin 2) :
      TopCat.Presheaf.germ (dualSheaf M).presheaf V x hxV (lamV i) = lam i :=
    (TopCat.Presheaf.germ_res_apply (dualSheaf M).presheaf
      (homOfLE hVU) x hxV (lamU i)).trans (hlam i)
  have hlw : (schemeExteriorStalkEquiv (dualSheaf M) 2 x).symm
      (exteriorPower.ιMulti (X.presheaf.stalk x) 2 lam) =
      TopCat.Presheaf.germ (Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ)).presheaf
        V x hxV (exteriorWedgeAlternating (dualSheaf M) V lamV) := by
    apply (schemeExteriorStalkEquiv (dualSheaf M) 2 x).injective
    simp only [LinearEquiv.apply_symm_apply]
    simpa only [hlamV] using (schemeExteriorStalkEquiv_native_wedge (dualSheaf M) x V hxV lamV).symm
  have hvw : (schemeExteriorStalkEquiv M 2 x).symm
      (exteriorPower.ιMulti (X.presheaf.stalk x) 2 v) =
      TopCat.Presheaf.germ (Scheme.Modules.exteriorPower M (2:ℤ)).presheaf
        V x hxV (exteriorWedgeAlternating M V vV) := by
    apply (schemeExteriorStalkEquiv M 2 x).injective
    simp only [LinearEquiv.apply_symm_apply]
    simpa only [hv] using (schemeExteriorStalkEquiv_native_wedge M x V hxV vV).symm
  rw [hlw, hvw, stalkHom_native_germ, dualStalkEquiv_native_germ, hphi]
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  rw [← hlamV 0, ← hlamV 1, ← hv 0, ← hv 1]
  rw [dualStalkEquiv_native_germ, dualStalkEquiv_native_germ,
    dualStalkEquiv_native_germ, dualStalkEquiv_native_germ]
  simp only [map_sub, map_mul]
end NcCubic.Geometry
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
theorem exteriorDuality_stalkHom_eq {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] [(Scheme.Modules.exteriorPower M (2:ℤ)).IsFinitePresentation]
    (x : X)
    [Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)]
    (phi : Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ) ⟶
      dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)))
    (hphi : HasExteriorDeterminantFormula M phi) :
    stalkHom phi x = (exteriorDualStalkEquiv M 2 x).toLinearMap := by
  let ED := schemeExteriorStalkEquiv (dualSheaf M) 2 x
  let EM := schemeExteriorStalkEquiv M 2 x
  have hh : (stalkHom phi x).comp ED.symm.toLinearMap =
      (exteriorDualStalkEquiv M 2 x).toLinearMap.comp ED.symm.toLinearMap := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro lam
    apply (dualStalkEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) x).injective
    let f₁ := dualStalkEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) x
      (stalkHom phi x (ED.symm (exteriorPower.ιMulti (X.presheaf.stalk x) 2 lam)))
    let f₂ := dualStalkEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) x
      (exteriorDualStalkEquiv M 2 x (ED.symm
        (exteriorPower.ιMulti (X.presheaf.stalk x) 2 lam)))
    have hv : f₁.comp EM.symm.toLinearMap = f₂.comp EM.symm.toLinearMap := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro v
      change f₁ (EM.symm (exteriorPower.ιMulti (X.presheaf.stalk x) 2 v)) =
        f₂ (EM.symm (exteriorPower.ιMulti (X.presheaf.stalk x) 2 v))
      calc
        _ = Matrix.det (n := Fin 2)
            (Matrix.of (fun i j => dualStalkEquiv M x (lam j) (v i))) :=
          exteriorDuality_stalk_wedges M phi hphi x lam v
        _ = _ := by
          dsimp only [f₂, exteriorDualStalkEquiv, LinearEquiv.trans_apply]
          have he := (dualStalkEquiv (Scheme.Modules.exteriorPower M (2:ℤ)) x).apply_symm_apply
            (exteriorDualStalkPairingEquiv M 2 x
              (ED.symm (exteriorPower.ιMulti (X.presheaf.stalk x) 2 lam)))
          exact (exteriorDualStalkPairingEquiv_ιMulti M 2 x lam v).symm.trans
            (congrArg (fun w => w (EM.symm (exteriorPower.ιMulti (X.presheaf.stalk x) 2 v))) he.symm)
    apply LinearMap.ext
    intro w
    obtain ⟨z, rfl⟩ := EM.symm.surjective w
    exact LinearMap.congr_fun hv z
  apply LinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := ED.symm.surjective z
  exact LinearMap.congr_fun hh w
end NcCubic.Geometry
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
set_option backward.isDefEq.respectTransparency false in
/-- The determinant exterior-dual morphism is an actual sheaf isomorphism for
an actual finite locally free module. -/
theorem isIso_of_exteriorDeterminantFormula {X : Scheme.{u}} (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M]
    (phi : Scheme.Modules.exteriorPower (dualSheaf M) (2:ℤ) ⟶
      dualSheaf (Scheme.Modules.exteriorPower M (2:ℤ)))
    (hphi : HasExteriorDeterminantFormula M phi) : IsIso phi := by
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u} M :=
    stackFiniteLocallyFree_of_finiteLocallyFree M hM
  have : M.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation M
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Modules.exteriorPower M (2:ℤ)) := exterior_finiteLocallyFree M 2 inferInstance
  have : (Scheme.Modules.exteriorPower M (2:ℤ)).IsFinitePresentation :=
    Stacks.FiniteLocallyFree.isFinitePresentation (Scheme.Modules.exteriorPower M (2:ℤ))
  apply isIso_of_bijective_stalkHom phi
  intro x
  have hfree := Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree M x
  have : Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) := hfree.1
  have : Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x) := hfree.2
  rw [exteriorDuality_stalkHom_eq M x phi hphi]
  exact (exteriorDualStalkEquiv M 2 x).bijective
end NcCubic.Geometry
