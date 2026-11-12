/- Canonical exterior/tensor comparison on actual local sections. -/
module
public import NcCubic.Geometry.ImmersionBivector
public import NcCubic.Geometry.NativeExteriorWedge
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open SheafOfModules.GradedAlgebra Stacks.PullbackExteriorAlgebra
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
/-- Adapted from pinned Stacks ExteriorAlgebraPullbackProd.pieceIso_homogeneousProd
(Apache-2.0), using only the already cached comparison structure fields. -/
lemma exteriorComparison_homogeneousProd {X Y : RingedSpace.{u,u}} (f : X ⟶ Y)
    (A : SheafOfModules.GradedAlgebra.{u,u} (structureRingSheaf Y))
    {M : SheafOfModules.{u} (structureRingSheaf Y)} {ι : M ⟶ A.piece 1}
    {B : SheafOfModules.GradedAlgebra.{u,u} (structureRingSheaf X)}
    {κ : (pullbackFunctor f).obj M ⟶ B.piece 1}
    (e : ExteriorAlgebraPullbackIso f A ι B κ)
    (U : (Opens Y.carrier)ᵒᵖ) (n : ℕ) (s : Fin n → M.val.obj U) :
    (e.app (n:ℤ)).hom.val.app ((opensMap f).op.obj U)
      (pullbackUnit f (A.piece (n:ℤ)) U
        (A.toPresheafGradedAlgebra.homogeneousProd U n (fun i => ι.val.app U (s i)))) =
    B.toPresheafGradedAlgebra.homogeneousProd ((opensMap f).op.obj U) n
      (fun i => κ.val.app ((opensMap f).op.obj U) (pullbackUnit f M U (s i))) := by
  induction n with
  | zero => exact e.map_one U
  | succ n ih =>
      refine (e.map_mul (n:ℤ) 1 U
        (A.toPresheafGradedAlgebra.homogeneousProd U n (fun i => ι.val.app U (s i.castSucc)))
        (ι.val.app U (s (Fin.last n)))).trans ?_
      exact congrArg₂ (fun x y => (B.mul (n:ℤ) 1).app ((opensMap f).op.obj U) x y)
        (ih (fun i => s i.castSucc)) (e.map_generator U (s (Fin.last n)))

lemma exteriorPullbackIso_unit_wedge {X P : Scheme.{u}} (i : X ⟶ P) (M : P.Modules)
    (U : P.Opens) (v : Fin 2 → Γ(M,U)) :
    (ImmersionBivector.exteriorPullbackIso i M (2:ℤ)).hom.val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (Scheme.Modules.exteriorPower M (2:ℤ))).val.app (op U) (exteriorWedgeAlternating M U v)) =
    exteriorWedgeAlternating ((Scheme.Modules.pullback i).obj M) (i ⁻¹ᵁ U)
      (fun j => (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U) (v j))) := by
  let e := Stacks.PullbackExteriorAlgebra.exteriorAlgebraPullbackIso i.toLRSHom.toShHom
    (Scheme.Modules.exteriorAlgebra M) (Scheme.Modules.exteriorGenerator M)
    (Scheme.Modules.exteriorAlgebra ((Scheme.Modules.pullback i).obj M))
    (Scheme.Modules.exteriorGenerator ((Scheme.Modules.pullback i).obj M))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra M)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra _)
  have hP := exteriorWedgeAlternating_homogeneousProd M U v
  have hX := exteriorWedgeAlternating_homogeneousProd ((Scheme.Modules.pullback i).obj M)
    (i ⁻¹ᵁ U) (fun j => (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U) (v j)))
  exact (congrArg (fun x =>
    (ImmersionBivector.exteriorPullbackIso i M (2:ℤ)).hom.val.app (op (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (Scheme.Modules.exteriorPower M (2:ℤ))).val.app (op U) x)) hP).trans
    ((exteriorComparison_homogeneousProd i.toLRSHom.toShHom _ e (op U) 2 v).trans hX.symm)
end NcCubic.Geometry.ImmersionBracketNaturality
