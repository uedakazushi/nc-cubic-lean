/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.NativeExteriorWedge
public import NcCubic.Geometry.SheafExteriorFrame
public import NcCubic.Geometry.BivectorLinearity
@[expose] public noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Coordinate components carry local pure tensors to actual wedges of the
images of the original coordinate inclusions. No rank or freeness assumption is used. -/
theorem exterior_component_map_wedge {X : Scheme.{u}} (L : X.Modules) (N : ℕ)
    {T : X.Modules} (g : SheafExteriorFrame.sum L N ⟶ T)
    (i j : Fin N) (U : X.Opens) (s t : Γ(L,U)) :
    (Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
      ((SheafExteriorFrame.component L N i j).val.app (op U)
        ((PresheafOfModules.tensorSheafUnit L L).app (op U) (s ⊗ₜ t))) =
      exteriorWedgeAlternating T U (fun k => g.val.app (op U)
        (![(biproduct.ι (fun _ : Fin N => L) i).val.app (op U) s,
          (biproduct.ι (fun _ : Fin N => L) j).val.app (op U) t] k)) := by
  let v : Fin 2 → Γ(SheafExteriorFrame.sum L N,U) :=
    ![(biproduct.ι (fun _ : Fin N => L) i).val.app (op U) s,
      (biproduct.ι (fun _ : Fin N => L) j).val.app (op U) t]
  have hw := SheafExteriorFrame.component_wedge L N i j (op U) s t
  have he : (SheafExteriorFrame.component L N i j).val.app (op U)
      ((PresheafOfModules.tensorSheafUnit L L).app (op U) (s ⊗ₜ t)) =
      exteriorWedgeAlternating (SheafExteriorFrame.sum L N) U v := by
    rw [exteriorWedgeAlternating_homogeneousProd]
    exact hw
  exact (congrArg ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)) he).trans
    (exteriorWedgeAlternating_map g U v)

/-- The actual local bracket on each coordinate component is its determinant
of tangent evaluations, after the exact original sheaf maps. -/
theorem bivectorSectionBracket_component {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) (N : ℕ) (g : SheafExteriorFrame.sum L N ⟶ tangentSheaf f)
    (i j : Fin N) (U : X.Opens) (s t : Γ(L,U)) (a b : Γ(X,U)) :
    bivectorSectionBracket f U
      ((Scheme.Modules.exteriorPowerMap g 2).val.app (op U)
        ((SheafExteriorFrame.component L N i j).val.app (op U)
          ((PresheafOfModules.tensorSheafUnit L L).app (op U) (s ⊗ₜ t)))) a b =
      tangentSectionDerivation f U (g.val.app (op U) ((biproduct.ι (fun _ : Fin N => L) i).val.app (op U) s)) a *
        tangentSectionDerivation f U (g.val.app (op U) ((biproduct.ι (fun _ : Fin N => L) j).val.app (op U) t)) b -
      tangentSectionDerivation f U (g.val.app (op U) ((biproduct.ι (fun _ : Fin N => L) j).val.app (op U) t)) a *
        tangentSectionDerivation f U (g.val.app (op U) ((biproduct.ι (fun _ : Fin N => L) i).val.app (op U) s)) b := by
  exact (congrArg (fun π => bivectorSectionBracket f U π a b)
    (exterior_component_map_wedge L N g i j U s t)).trans
    (bivectorSectionBracket_native_wedge f U _ a b)
end NcCubic.Geometry
