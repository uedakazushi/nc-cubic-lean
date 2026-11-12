module
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
public import NcCubic.Geometry.SheafBiderivationEvaluation
public import NcCubic.Geometry.ExteriorWedgeLaws
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
variable {X : Scheme.{u}}
/-- Pull back evaluation at an actual section along an actual morphism into a dual. -/
def dualFunctionalPullback {M N : X.Modules} (Φ : M ⟶ dualSheaf N)
    (U : X.Opens) (s : Γ(N,U)) : Γ(dualSheaf M,U) :=
  (dualMap Φ).app U ((toDoubleDual N).app U s)

theorem dualFunctionalPullback_pair {M N : X.Modules} (Φ : M ⟶ dualSheaf N)
    (U : X.Opens) (s : Γ(N,U)) (W : Over U) (p : Γ(M,W.left)) :
    dualPairing M (dualFunctionalPullback Φ U s) W p =
      evalAt N (Φ.app W.left p) (N.presheaf.map W.hom.op s) :=
  (dualPairing_dualMap Φ _ W p).trans (toDoubleDual_dualPairing N s W _)

theorem dualFunctionalPullback_eval {M N : X.Modules} (Φ : M ⟶ dualSheaf N)
    (U : X.Opens) (s : Γ(N,U)) (p : Γ(M,U)) :
    evalAt M (dualFunctionalPullback Φ U s) p = evalAt N (Φ.app U p) s := by
  have h := dualFunctionalPullback_pair Φ U s (Over.mk (𝟙 U)) p
  change dualPairing M (dualFunctionalPullback Φ U s) (Over.mk (𝟙 U)) p =
    evalAt N (Φ.app U p) (N.presheaf.map (𝟙 (op U)) s) at h
  rw [N.presheaf.map_id] at h
  exact h

variable {S : Scheme.{u}} (f : X ⟶ S)
theorem cotangentWedgeSection_natural {U V : X.Opens} (h : V ⟶ U)
    (v : Fin 2 → Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)).presheaf.map h.op
      (cotangentWedgeSection f U v) = cotangentWedgeSection f V
        (fun i => (Scheme.Hom.relativeDifferentials f).presheaf.map h.op (v i)) :=
  exteriorWedgeAlternating_natural (Scheme.Hom.relativeDifferentials f) h v

theorem cotangentDifferentialWedge_natural {U V : X.Opens} (h : V ⟶ U) (a b : Γ(X,U)) :
    (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) (2:ℤ)).presheaf.map h.op
      (cotangentWedgeSection f U ![(Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a,
        (Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b]) =
    cotangentWedgeSection f V
      ![(Scheme.Hom.universalRelativeDerivation f).d (X:=op V) (X.presheaf.map h.op a),
        (Scheme.Hom.universalRelativeDerivation f).d (X:=op V) (X.presheaf.map h.op b)] := by
  have hv : (fun i => (Scheme.Hom.relativeDifferentials f).presheaf.map h.op
      (![(Scheme.Hom.universalRelativeDerivation f).d (X:=op U) a,
        (Scheme.Hom.universalRelativeDerivation f).d (X:=op U) b] i)) =
    ![(Scheme.Hom.universalRelativeDerivation f).d (X:=op V) (X.presheaf.map h.op a),
      (Scheme.Hom.universalRelativeDerivation f).d (X:=op V) (X.presheaf.map h.op b)] := by
    funext i
    fin_cases i
    · exact ((Scheme.Hom.universalRelativeDerivation f).d_map h.op a).symm
    · exact ((Scheme.Hom.universalRelativeDerivation f).d_map h.op b).symm
  exact (cotangentWedgeSection_natural f h _).trans (congrArg (cotangentWedgeSection f V) hv)
end NcCubic.Geometry
