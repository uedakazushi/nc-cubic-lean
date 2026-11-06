/- Restricting compatible forms along injective Lie algebra maps. -/
module
public import NcCubic.LieObstruction
public import Mathlib.LinearAlgebra.BilinearMap
@[expose] public section
namespace NcCubic.LieObstruction
variable {K I L : Type*} [Field K] [LieRing I] [LieAlgebra K I]
  [LieRing L] [LieAlgebra K L]

/-- Pull back the family of bilinear forms along a Lie algebra map. -/
def restrictedForms (φ : I →ₗ⁅K⁆ L) (forms : Set (L →ₗ[K] L →ₗ[K] K)) :
    Set (I →ₗ[K] I →ₗ[K] K) :=
  (fun H => H.compl₁₂ φ.toLinearMap φ.toLinearMap) '' forms

theorem compatible_restrict (φ : I →ₗ⁅K⁆ L)
    (H : L →ₗ[K] L →ₗ[K] K) (hH : Compatible H) :
    Compatible (H.compl₁₂ φ.toLinearMap φ.toLinearMap) := by
  intro a b c d
  simpa only [LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, LieHom.map_lie] using
    hH (φ a) (φ b) (φ c) (φ d)

theorem restrictedForms_compatible (φ : I →ₗ⁅K⁆ L)
    (forms : Set (L →ₗ[K] L →ₗ[K] K))
    (hcompatible : ∀ H ∈ forms, Compatible H) :
    ∀ H ∈ restrictedForms φ forms, Compatible H := by
  rintro _ ⟨H,hH,rfl⟩
  exact compatible_restrict φ H (hcompatible H hH)

theorem restrictedForms_basepointFree (φ : I →ₗ⁅K⁆ L) (hφ : Function.Injective φ)
    (forms : Set (L →ₗ[K] L →ₗ[K] K)) (hfree : BasepointFree forms) :
    BasepointFree (restrictedForms φ forms) := by
  intro v hv
  have hv' : φ v ≠ 0 := by
    intro hz
    apply hv
    apply hφ
    simpa only [map_zero] using hz
  obtain ⟨H,hH,hn⟩ := hfree (φ v) hv'
  exact ⟨H.compl₁₂ φ.toLinearMap φ.toLinearMap, ⟨H,hH,rfl⟩, hn⟩
end NcCubic.LieObstruction
