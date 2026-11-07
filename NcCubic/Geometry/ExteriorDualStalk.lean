/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.DualStalk
public import NcCubic.Geometry.ExteriorFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u

def exteriorLinearEquiv {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (n : ℕ) (e : V ≃ₗ[R] W) :
    (⋀[R]^n V) ≃ₗ[R] (⋀[R]^n W) :=
  LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap)
    ⟨exteriorPower.map_injective e.symm.toLinearMap (by ext x; simp),
      exteriorPower.map_surjective e.surjective⟩

/-- The genuine exterior sheaf stalk comparison at the scheme's spelling. -/
def schemeExteriorStalkEquiv {X : Scheme.{u}} (M : X.Modules) (n : ℕ) (x : X) :
    (Scheme.Modules.exteriorPower M (n:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      ⋀[X.presheaf.stalk x]^n (M.presheaf.stalk x) :=
  (SheafOfModules.algebras (Opens.grothendieckTopology ↥X) M).exteriorPowerStalkEquiv n x

/-- The canonical algebraic dual pairing identifies actual exterior-dual stalks
with the dual of actual exterior stalks, under genuine finite-free stalk hypotheses. -/
def exteriorDualStalkPairingEquiv {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (n : ℕ) (x : X)
    [Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)] :
    (Scheme.Modules.exteriorPower (dualSheaf M) (n:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      Module.Dual (X.presheaf.stalk x)
        ((Scheme.Modules.exteriorPower M (n:ℤ)).presheaf.stalk x) :=
  (schemeExteriorStalkEquiv (dualSheaf M) n x).trans
    ((exteriorLinearEquiv n (dualStalkEquiv M x)).trans
      ((LinearEquiv.ofBijective (exteriorPower.pairingDual (X.presheaf.stalk x)
        (M.presheaf.stalk x) n) (exteriorPower.bijective_pairingDual _ _ _)).trans
          (LinearEquiv.arrowCongr (schemeExteriorStalkEquiv M n x).symm
            (LinearEquiv.refl (X.presheaf.stalk x) (X.presheaf.stalk x)))))

/-- If the exterior sheaf is finitely presented as well, both sides are actual
sheaf stalks. This is the stalk candidate for the global canonical duality map. -/
def exteriorDualStalkEquiv {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (n : ℕ)
    [(Scheme.Modules.exteriorPower M (n:ℤ)).IsFinitePresentation] (x : X)
    [Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)] :
    (Scheme.Modules.exteriorPower (dualSheaf M) (n:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (dualSheaf (Scheme.Modules.exteriorPower M (n:ℤ))).presheaf.stalk x :=
  (exteriorDualStalkPairingEquiv M n x).trans
    (dualStalkEquiv (Scheme.Modules.exteriorPower M (n:ℤ)) x).symm

/-- The stalk pairing on exterior generators is the genuine determinant evaluation. -/
theorem exteriorDualStalkPairingEquiv_ιMulti {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (n : ℕ) (x : X)
    [Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x)]
    [Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x)]
    (lam : Fin n → (dualSheaf M).presheaf.stalk x) (v : Fin n → M.presheaf.stalk x) :
    exteriorDualStalkPairingEquiv M n x
      ((schemeExteriorStalkEquiv (dualSheaf M) n x).symm
        (exteriorPower.ιMulti (X.presheaf.stalk x) n lam))
      ((schemeExteriorStalkEquiv M n x).symm
        (exteriorPower.ιMulti (X.presheaf.stalk x) n v)) =
    Matrix.det (n := Fin n) (Matrix.of (fun i j => dualStalkEquiv M x (lam j) (v i))) := by
  simp only [exteriorDualStalkPairingEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply,LinearEquiv.arrowCongr_apply,LinearEquiv.refl_apply,
    LinearEquiv.symm_symm]
  change exteriorPower.pairingDual (X.presheaf.stalk x) (M.presheaf.stalk x) n
    (exteriorPower.map n (dualStalkEquiv M x).toLinearMap
      (exteriorPower.ιMulti (X.presheaf.stalk x) n lam))
    (exteriorPower.ιMulti (X.presheaf.stalk x) n v) = _
  rw [exteriorPower.map_apply_ιMulti]
  exact exteriorPower.pairingDual_ιMulti_ιMulti (R := X.presheaf.stalk x)
    (fun i => dualStalkEquiv M x (lam i)) v

/-- Under actual finite local freeness, both sides are genuine sheaf stalks.
All finite-presentation and algebraic free-stalk hypotheses are derived here. -/
def exteriorDualStalkEquivOfFiniteLocallyFree {X : Scheme.{u}} (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u} M]
    (n : ℕ) (x : X) :
    (Scheme.Modules.exteriorPower (dualSheaf M) (n:ℤ)).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      (dualSheaf (Scheme.Modules.exteriorPower M (n:ℤ))).presheaf.stalk x := by
  letI : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u} M :=
    stackFiniteLocallyFree_of_finiteLocallyFree M hM
  letI : M.IsFinitePresentation := Stacks.FiniteLocallyFree.isFinitePresentation M
  letI : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Modules.exteriorPower M (n:ℤ)) := exterior_finiteLocallyFree M n inferInstance
  letI : (Scheme.Modules.exteriorPower M (n:ℤ)).IsFinitePresentation :=
    Stacks.FiniteLocallyFree.isFinitePresentation (Scheme.Modules.exteriorPower M (n:ℤ))
  have hfree := Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree M x
  letI : Module.Free (X.presheaf.stalk x) (M.presheaf.stalk x) := hfree.1
  letI : Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x) := hfree.2
  exact exteriorDualStalkEquiv M n x

end NcCubic.Geometry
