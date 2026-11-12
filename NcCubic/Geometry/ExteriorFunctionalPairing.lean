module
public import NcCubic.Geometry.ExteriorWedgeLaws
public import NcCubic.Geometry.SheafBiderivationEvaluation
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
section Algebra
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
private theorem update_pair_last (a b : M) : Function.update ![a,0] (1:Fin 2) b = ![a,b] := by
  funext i
  fin_cases i <;> simp

def alternatingToBilinear (A : AlternatingMap R M N (Fin 2)) : M →ₗ[R] M →ₗ[R] N where
  toFun a := {
    toFun b := A ![a,b]
    map_add' b c := by simpa only [update_pair_last] using A.map_update_add ![a,0] 1 b c
    map_smul' r b := by simpa only [update_pair_last,RingHom.id_apply] using A.map_update_smul ![a,0] 1 r b }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change A ![a+b,c] = A ![a,c]+A ![b,c]
    exact A.map_vecCons_add ![c] a b
  map_smul' r a := by
    apply LinearMap.ext
    intro b
    change A ![r • a,b] = r • A ![a,b]
    exact A.map_vecCons_smul ![b] r a
end Algebra
variable {X S : Scheme.{u}} (f : X ⟶ S)
def exteriorFunctionalEvaluation
    (lam : Γ(dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)),⊤))
    (U : X.Opens) :
    Γ(Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ),U) →ₗ[Γ(X,U)] Γ(X,U) :=
  (lam.app (op (Over.mk (homOfLE (show U≤⊤ from le_top))))).hom

def exteriorFunctionalPairing
    (lam : Γ(dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)),⊤))
    (U : X.Opens) : Γ(Scheme.Hom.relativeDifferentials f,U) →ₗ[Γ(X,U)]
      Γ(Scheme.Hom.relativeDifferentials f,U) →ₗ[Γ(X,U)] Γ(X,U) :=
  (alternatingToBilinear (exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials f) U)).compr₂
    (exteriorFunctionalEvaluation f lam U)

theorem exteriorFunctionalEvaluation_natural
    (lam : Γ(dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)),⊤))
    {U V : X.Opens} (h : V≤U)
    (z : Γ(Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ),U)) :
    (X.presheaf.map (homOfLE h).op) (exteriorFunctionalEvaluation f lam U z) =
      exteriorFunctionalEvaluation f lam V
        ((Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)).presheaf.map (homOfLE h).op z) :=
  (localHomFamily_restrict (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ))
    (SheafOfModules.unit (structureSheaf X.sheaf)) ⊤ lam V U h le_top z).symm

theorem exteriorFunctionalPairing_natural
    (lam : Γ(dualSheaf (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)),⊤))
    {U V : X.Opens} (h : V≤U) (a b : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (X.presheaf.map (homOfLE h).op) (exteriorFunctionalPairing f lam U a b) =
      exteriorFunctionalPairing f lam V
        ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op a)
        ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op b) := by
  have hw := exteriorWedgeAlternating_natural (Scheme.Hom.relativeDifferentials f) (homOfLE h) ![a,b]
  have hv : (fun i => (Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op (![a,b] i)) =
      ![(Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op a,
        (Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op b] := by
    funext i
    fin_cases i <;> rfl
  exact (exteriorFunctionalEvaluation_natural f lam h _).trans
    ((congrArg (exteriorFunctionalEvaluation f lam V) hw).trans
      (congrArg (fun v => exteriorFunctionalEvaluation f lam V
        (exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials f) V v)) hv))
end NcCubic.Geometry
