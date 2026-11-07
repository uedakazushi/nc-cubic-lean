module
public import NcCubic.Geometry.SheafExteriorFrame
public import NcCubic.Geometry.ExteriorUnitGenerators
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace NcCubic.Geometry.SheafExteriorFrame
universe u
local instance (X : Scheme.{u}) : CategoryTheory.Limits.HasFiniteBiproducts X.Modules :=
  CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- The canonical ordered coordinate component is exactly the raw
sectionwise wedge mapped by the genuine exterior sheafification unit. -/
theorem component_eq_unit_wedgeSection {X : Scheme.{u}} (L : X.Modules)
    (N : ℕ) (i j : Fin N) (U : X.Opensᵒᵖ) (v w : L.val.obj U) :
    (component L N i j).val.app U
      ((PresheafOfModules.tensorSheafUnit L L).app U (v ⊗ₜ w)) =
    (exteriorPresheafUnit (sum L N)).app U
      (PresheafExterior.wedgeSection (O := X.sheaf.obj)
        (SheafOfModules.valPresheaf (Osharp := X.sheaf)
          (Opens.grothendieckTopology ↥X) (sum L N)) 2 U
        ![(biproduct.ι (fun _ : Fin N => L) i).val.app U v,
          (biproduct.ι (fun _ : Fin N => L) j).val.app U w]) := by
  have hu := exteriorPresheafUnit_wedgeSection (sum L N) U
    ![(biproduct.ι (fun _ : Fin N => L) i).val.app U v,
      (biproduct.ι (fun _ : Fin N => L) j).val.app U w]
  have hf : (fun k : Fin 2 => (Scheme.Modules.exteriorGenerator (sum L N)).val.app U
      (![(biproduct.ι (fun _ : Fin N => L) i).val.app U v,
        (biproduct.ι (fun _ : Fin N => L) j).val.app U w] k)) =
      ![(Scheme.Modules.exteriorGenerator (sum L N)).val.app U
        ((biproduct.ι (fun _ : Fin N => L) i).val.app U v),
      (Scheme.Modules.exteriorGenerator (sum L N)).val.app U
        ((biproduct.ι (fun _ : Fin N => L) j).val.app U w)] := by
    funext k
    fin_cases k <;> rfl
  exact (component_wedge L N i j U v w).trans
    ((congrArg ((Scheme.Modules.exteriorAlgebra (sum L N)).toPresheafGradedAlgebra.homogeneousProd
      U 2) hf).symm.trans hu.symm)

end NcCubic.Geometry.SheafExteriorFrame
