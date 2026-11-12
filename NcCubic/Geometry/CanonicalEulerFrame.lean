module
public import NcCubic.Geometry.BiconeDualColumns
public import NcCubic.Geometry.CanonicalTwistDuality
public import NcCubic.Geometry.CoordinateWedgeUnit
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

namespace NcCubic.Geometry.SheafExteriorFrame
universe u
local instance (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The frozen NATIVE bicone used by the canonical exterior coordinate frame. -/
def coordinateBicone {X : Scheme.{u}} (L : X.Modules) (N : ℕ) :
    Bicone (fun _ : Fin N => L) := biproduct.bicone _

def coordinateBicone_isBilimit {X : Scheme.{u}} (L : X.Modules) (N : ℕ) :
    (coordinateBicone L N).IsBilimit := biproduct.isBilimit _

@[simp] theorem coordinateBicone_pt {X : Scheme.{u}} (L : X.Modules) (N : ℕ) :
    (coordinateBicone L N).pt = sum L N := rfl

/-- These are the literal native inclusions, not the lower/site inclusions. -/
theorem coordinateBicone_ι {X : Scheme.{u}} (L : X.Modules) (N : ℕ) (i : Fin N) :
    (coordinateBicone L N).ι i = (biproduct.ι (fun _ : Fin N => L) i : L ⟶ sum L N) := rfl

/-- Certified coupling of this frozen bicone to the ORIGINAL frame components. -/
theorem component_eq_unit_coordinateWedge {X : Scheme.{u}} (L : X.Modules)
    (N : ℕ) (i j : Fin N) (U : X.Opensᵒᵖ) (v w : L.val.obj U) :
    (component L N i j).val.app U
      ((PresheafOfModules.tensorSheafUnit L L).app U (v ⊗ₜ w)) =
    (exteriorPresheafUnit (sum L N)).app U
      (PresheafExterior.wedgeSection (O := X.sheaf.obj)
        (SheafOfModules.valPresheaf (Osharp := X.sheaf)
          (Opens.grothendieckTopology ↥X) (sum L N)) 2 U
        ![((coordinateBicone L N).ι i).val.app U v,
          ((coordinateBicone L N).ι j).val.app U w]) :=
  component_eq_unit_wedgeSection L N i j U v w

end NcCubic.Geometry.SheafExteriorFrame

namespace NcCubic.Geometry.CanonicalEulerMiddle
universe u
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat

/-- Map the ORIGINAL lower negative Euler bicone along the identity comparison. -/
def originalNegativeBicone (A : Type u) [CommRing A] (n : ℕ) :=
  let b := biproduct.bicone (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n)
  (schemeModulesOfSite (_root_.AlgebraicGeometry.Proj (polyGrading A n))).mapBicone b

def originalNegativeBicone_isBilimit (A : Type u) [CommRing A] (n : ℕ) :
    (originalNegativeBicone A n).IsBilimit := by
  let b := biproduct.bicone (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n)
  have hb : b.IsBilimit :=
    biproduct.isBilimit (Stacks.AlgebraicGeometry.ProjEulerSequence.twistMinusOneFamily A n)
  exact mapSiteBicone_isBilimit (_root_.AlgebraicGeometry.Proj (polyGrading A n)) b hb


end NcCubic.Geometry.CanonicalEulerMiddle
