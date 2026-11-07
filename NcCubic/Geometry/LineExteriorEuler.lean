/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
A map-preserving scheme-category adapter for the pinned Stacks exterior line sequence. -/
module
public import NcCubic.Geometry.ModulesBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerLineSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace NcCubic.Geometry
universe u
open Stacks.SheafOfModules.TopWedge
variable {X : Scheme.{u}} {L E Q : X.Modules}
  (f : L ⟶ E) (g : E ⟶ Q) (w : f ≫ g = 0)
  (hS : (ShortComplex.mk f g w).Exact)
  [Mono f] [Epi g]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1]
  (m : ℕ) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q m]

/-- The actual exterior line sequence, retained as a scheme-module short complex.
Its last map is the exterior power of the original quotient map. -/
def wedgeLineComplex (k : ℕ) : ShortComplex X.Modules := by
  have hmono : Mono (C := _root_.SheafOfModules.{u}
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf)) f := ‹Mono f›
  have hepi : Epi (C := _root_.SheafOfModules.{u}
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf)) g := ‹Epi g›
  let := hmono
  let := hepi
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (R := CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf) L 1 :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) L 1)
  have hQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (R := CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf) Q m :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) Q m)
  let := hL
  let := hQ
  let S₀ : ShortComplex (_root_.SheafOfModules.{u} X.ringCatSheaf) := ShortComplex.mk
    (lineComparison (Osharp := X.sheaf) (_root_.SheafOfModules.algebras _ L)
      (_root_.SheafOfModules.algebras _ E) (_root_.SheafOfModules.algebras _ Q) f g w hS k)
    ((extHom (Osharp := X.sheaf) (_root_.SheafOfModules.algebras _ E)
      (_root_.SheafOfModules.algebras _ Q) g).app ((1 + (k + 1) : ℕ) : ℤ))
    (lineComparison_comp_extHom (Osharp := X.sheaf) (_root_.SheafOfModules.algebras _ L)
      (_root_.SheafOfModules.algebras _ E) (_root_.SheafOfModules.algebras _ Q)
      f g w hS m k)
  exact S₀.map (schemeModulesOfSite X)

theorem wedgeLineComplex_shortExact (k : ℕ) :
    (wedgeLineComplex f g w hS m k).ShortExact := by
  have hmono : Mono (C := _root_.SheafOfModules.{u}
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf)) f := ‹Mono f›
  have hepi : Epi (C := _root_.SheafOfModules.{u}
      (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf)) g := ‹Epi g›
  let := hmono
  let := hepi
  have hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (R := CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf) L 1 :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) L 1)
  have hQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (R := CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology (X : TopCat)) X.sheaf) Q m :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (R := X.ringCatSheaf) Q m)
  let := hL
  let := hQ
  exact schemeModulesOfSite_shortExact X _
    (shortExact_lineComparison (Osharp := X.sheaf) (_root_.SheafOfModules.algebras _ L)
      (_root_.SheafOfModules.algebras _ E) (_root_.SheafOfModules.algebras _ Q)
      f g w hS m k)

@[simp] theorem wedgeLineComplex_g (k : ℕ) :
    (wedgeLineComplex f g w hS m k).g =
      Scheme.Modules.exteriorPowerMap g ((1 + (k + 1) : ℕ) : ℤ) := rfl

/-- The first term is the original line sheaf tensored with the preceding
exterior power of the quotient; no arbitrary object identification is assumed. -/
def wedgeLineComplex_sourceIso (k : ℕ) :
    (wedgeLineComplex f g w hS m k).X₁ ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj
        (Scheme.Modules.exteriorPower Q ((k + 1 : ℕ) : ℤ)) :=
  (Functor.mapIso (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
    ((_root_.SheafOfModules.algebras _ L).exteriorPowerOneIso)).app
      (Scheme.Modules.exteriorPower Q ((k + 1 : ℕ) : ℤ))

end NcCubic.Geometry
