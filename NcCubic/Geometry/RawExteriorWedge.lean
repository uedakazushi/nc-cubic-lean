/- Copyright (c) 2026 nc-cubic contributors. All rights reserved. -/
module
public import NcCubic.Geometry.PresheafExteriorDesc
@[expose] public noncomputable section
namespace NcCubic.Geometry.PresheafExterior
open CategoryTheory
universe u v w a
variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)) (n : ℕ)
/-- A decomposable section of the genuine sectionwise exterior-power presheaf. -/
def wedgeSection (U : Cᵒᵖ) (v : Fin n → F.obj U) :
    (PresheafOfModules.extPow (O:=O) n F).obj U :=
  (PresheafOfModules.extPowSections n F U).symm (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj U) n v)
@[simp] theorem desc_wedgeSection
    (A : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i)))
    (U : Cᵒᵖ) (v : Fin n → F.obj U) :
    (desc A hA).app U (wedgeSection F n U v) = A U v :=
  desc_app_ιMulti A hA U v
end NcCubic.Geometry.PresheafExterior
