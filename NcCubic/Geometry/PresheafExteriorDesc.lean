module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
@[expose] public section
noncomputable section
open CategoryTheory Opposite
namespace NcCubic.Geometry.PresheafExterior
universe u v w a
variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F G : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)} {n : ℕ}

/-- The exterior universal property on genuine abstract presheaf sections. -/
def descSections
    (A : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n)) (U : Cᵒᵖ) :
    (⋀[(O ⋙ forget₂ _ RingCat).obj U]^n (F.obj U)) →ₗ[(O ⋙ forget₂ _ RingCat).obj U] G.obj U :=
  exteriorPower.alternatingMapLinearEquiv (A U)

theorem descSections_natural
    (A : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i)))
    {U V : Cᵒᵖ} (h : U ⟶ V) (z : ⋀[(O ⋙ forget₂ _ RingCat).obj U]^n (F.obj U)) :
    G.map h (descSections A U z) = descSections A V
      (ExteriorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map h).hom (F.restrictₛₗ h) z) := by
  have key : (G.restrictₛₗ h).comp (descSections A U) =
      (descSections A V).comp
        (ExteriorAlgebra.powMapₛₗ n ((O ⋙ forget₂ _ RingCat).map h).hom (F.restrictₛₗ h)) := by
    refine ExteriorAlgebra.powExtₛₗ fun v => ?_
    simp only [LinearMap.comp_apply,descSections,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,ExteriorAlgebra.powMapₛₗ_ιMulti]
    exact hA h v
  exact DFunLike.congr_fun key z

/-- A restriction-compatible alternating family descends to an actual morphism
from the sectionwise exterior-power presheaf. -/
def desc
    (A : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i))) :
    PresheafOfModules.extPow (O:=O) n F ⟶ G where
  app U := ModuleCat.ofHom ((descSections A U).comp
    (PresheafOfModules.extPowSections n F U).toLinearMap)
  naturality h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    have hz := descSections_natural A hA h (PresheafOfModules.extPowSections n F _ z)
    exact hz.symm

@[simp] theorem desc_app
    (A : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i)))
    (U : Cᵒᵖ) (z : (PresheafOfModules.extPow (O:=O) n F).obj U) :
    (desc A hA).app U z = descSections A U (PresheafOfModules.extPowSections n F U z) := rfl

/-- On an actual decomposable exterior section, descent recovers the given
alternating family, through the explicit sectionwise comparison. -/
@[simp] theorem desc_app_ιMulti
    (A : ∀ U : Cᵒᵖ, AlternatingMap ((O ⋙ forget₂ _ RingCat).obj U)
      (F.obj U) (G.obj U) (Fin n))
    (hA : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (v : Fin n → F.obj U),
      G.map h (A U v) = A V (fun i => F.map h (v i)))
    (U : Cᵒᵖ) (v : Fin n → F.obj U) :
    (desc A hA).app U ((PresheafOfModules.extPowSections n F U).symm
      (exteriorPower.ιMulti ((O ⋙ forget₂ _ RingCat).obj U) n v)) = A U v := by
  simp only [desc_app,LinearEquiv.apply_symm_apply,descSections,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
end NcCubic.Geometry.PresheafExterior
