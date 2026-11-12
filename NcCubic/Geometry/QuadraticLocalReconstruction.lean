module
public import NcCubic.Geometry.ProjectiveQuadraticSections
public import NcCubic.Geometry.QuadraticSectionReadout
public import NcCubic.Geometry.BivectorLinearity
public import NcCubic.Geometry.ProjectiveCoordinateDerivatives
@[expose] public noncomputable section
namespace NcCubic.Geometry
open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjTwistRank
open Stacks.AlgebraicGeometry.ProjPolyChart
attribute [local instance] MvPolynomial.gradedAlgebra hasFiniteBiproducts_toRingCat
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (n N : ℕ)
theorem quadraticLocal_reconstruct (U : (AlgebraicGeometry.Proj (polyGrading ℂ n)).Opens)
    (σ : (wedge ℂ n (twistSum ℂ n 1 N) 2).val.obj (op U)) :
    ∑ s : Set.powersetCard (Fin N) 2,
      (ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticProjection ℂ n N s).val.app (op U) σ) = σ := by
  let F := Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading ℂ n)) U
  let M : (AlgebraicGeometry.Proj (polyGrading ℂ n)).Modules := wedge ℂ n (twistSum ℂ n 1 N) 2
  have h := congrArg (fun k : M ⟶ M => (F.map k).hom σ)
    (ProjectiveExteriorFrame.quadraticProjections_reconstruct ℂ n N)
  simp only [Functor.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply,
    Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change (∑ s : Set.powersetCard (Fin N) 2,
      (ProjectiveExteriorFrame.quadraticComponent ℂ n N s).val.app (op U)
        ((ProjectiveExteriorFrame.quadraticProjection ℂ n N s).val.app (op U) σ)) = σ at h
  exact h
theorem quadraticProjection_restrict (U : (AlgebraicGeometry.Proj (polyGrading ℂ n)).Opens)
    (σ : (twistCoefficientSections ℂ n).obj (wedge ℂ n (twistSum ℂ n 1 N) 2))
    (s : Set.powersetCard (Fin N) 2) :
    (ProjectiveExteriorFrame.quadraticProjection ℂ n N s).val.app (op U)
      ((wedge ℂ n (twistSum ℂ n 1 N) 2).val.map (homOfLE (show U ≤ ⊤ from le_top)).op σ) =
    ProjectiveCoordinateDerivatives.restrictedDegreeSection 2
      (ProjectiveQuadraticSections.quadraticSectionsEquiv ℂ n N σ s) U := by
  let p := ProjectiveExteriorFrame.quadraticProjection ℂ n N s
  let h := (homOfLE (show U ≤ ⊤ from le_top)).op
  have hn := congrArg (fun k => k.hom σ) (p.val.naturality h)
  change p.val.app (op U) ((wedge ℂ n (twistSum ℂ n 1 N) 2).val.map h σ) = (twistObj ℂ n 2).val.map h (p.val.app (op ⊤) σ) at hn
  rw [hn]
  have hc := ProjectiveQuadraticSections.quadraticSectionsEquiv_component ℂ n N σ s
  exact congrArg ((twistObj ℂ n 2).val.map h)
    (show p.val.app (op ⊤) σ = _ from hc.symm)

end NcCubic.Geometry
