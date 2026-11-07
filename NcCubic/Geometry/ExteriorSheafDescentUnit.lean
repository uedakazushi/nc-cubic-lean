module
public import NcCubic.Geometry.ExteriorSheafDescent
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
open CategoryTheory AlgebraicGeometry Opposite
namespace NcCubic.Geometry
universe u v w

/-- The unit followed by a transported adjunction descent recovers the original map. -/
theorem adjunction_unit_transport_desc
    {C : Type u} {D : Type v} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {X : C} {A B : D} (e : A ≅ L.obj X) (f : X ⟶ R.obj B) :
    adj.unit.app X ≫ R.map e.inv ≫
      R.map (e.hom ≫ L.map f ≫ adj.counit.app B) = f := by
  calc
    _ = adj.unit.app X ≫ R.map (e.inv ≫ e.hom ≫ L.map f ≫ adj.counit.app B) := by
      simp only [Functor.map_comp]
    _ = adj.unit.app X ≫ R.map (L.map f ≫ adj.counit.app B) := by simp
    _ = (adj.unit.app X ≫ R.map (L.map f)) ≫ R.map (adj.counit.app B) := by
      rw [Functor.map_comp,Category.assoc]
    _ = (f ≫ adj.unit.app (R.obj B)) ≫ R.map (adj.counit.app B) := by
      exact congrArg (fun k => k ≫ R.map (adj.counit.app B)) (adj.unit.naturality f).symm
    _ = f := by rw [Category.assoc,adj.right_triangle_components,Category.comp_id]

/-- The right-adjoint underlying-presheaf functor used by the actual module
sheafification adjunction on a scheme. -/
abbrev moduleUnderlyingFunctor (X : Scheme.{u}) :=
  SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) ⋙
    PresheafOfModules.restrictScalars
      (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 X.sheaf.obj))

/-- The actual exterior sheafification unit, read through the canonical
exterior-sheaf/sheafification isomorphism. -/
def exteriorPresheafUnit {X : Scheme.{u}} (F : X.Modules) :
    PresheafOfModules.extPow (O:=X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) F) ⟶
      SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X)
        (Scheme.Modules.exteriorPower F (2:ℤ)) :=
  (PresheafOfModules.sheafificationAdjunction
      (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 X.sheaf.obj))).unit.app _ ≫
    (moduleUnderlyingFunctor X).map
      (SheafOfModules.exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X)
        (SheafOfModules.algebras _ F) 2).inv

theorem exteriorPresheafUnit_descend {X : Scheme.{u}} (F G : X.Modules)
    (α : PresheafOfModules.extPow (O:=X.sheaf.obj) 2
      (SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) F) ⟶
      SheafOfModules.valPresheaf (Opens.grothendieckTopology ↥X) G) :
    exteriorPresheafUnit F ≫ (moduleUnderlyingFunctor X).map
      (descendExteriorPresheafMorphism F G α) = α := by
  exact adjunction_unit_transport_desc
    (PresheafOfModules.sheafificationAdjunction
      (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 X.sheaf.obj)))
    (SheafOfModules.exteriorPowerSheafifyIso (Opens.grothendieckTopology ↥X)
      (SheafOfModules.algebras _ F) 2) α

/-- Pointwise evaluation of a presheaf composition equality, kept abstract to
avoid expanding scheme-section carrier aliases during elaboration. -/
theorem presheaf_comp_apply_of_eq
    {C : Type u} [Category C] {R : Cᵒᵖ ⥤ RingCat.{v}}
    {F G H : PresheafOfModules.{w} R} (α : F ⟶ G) (β : G ⟶ H) (γ : F ⟶ H)
    (h : α ≫ β = γ) (U : Cᵒᵖ) (z : F.obj U) :
    β.app U (α.app U z) = γ.app U z :=
  congrArg (fun δ : F ⟶ H => δ.app U z) h
end NcCubic.Geometry
