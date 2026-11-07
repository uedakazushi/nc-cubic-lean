module
public import NcCubic.Geometry.LocalSectionHom
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X : Scheme.{u}} (M N : X.Modules) (U : X.Opens)
/-- A compatible linear family on subopens is an actual restricted presheaf morphism. -/
def localHomOfFamily
    (t : ∀ V : X.Opens, V ≤ U → Γ(M,V) → Γ(N,V))
    (hadd : ∀ V h a b, t V h (a+b) = t V h a + t V h b)
    (hsmul : ∀ V h (r : Γ(X,V)) a, t V h (r • a) = r • t V h a)
    (hres : ∀ (V W : X.Opens) (hVW : V ≤ W) (hWU : W ≤ U) (a : Γ(M,W)),
      t V (hVW.trans hWU) (M.presheaf.map (homOfLE hVW).op a) =
        N.presheaf.map (homOfLE hVW).op (t W hWU a)) :
    (restrFun X.sheaf.obj U).obj M.val ⟶ (restrFun X.sheaf.obj U).obj N.val where
  app Z := ModuleCat.homAddEquiv.symm {
    toFun := fun a => t Z.unop.left (leOfHom Z.unop.hom) a
    map_add' := hadd _ _
    map_smul' := hsmul _ _ }
  naturality {Z Z'} k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have hh := hres Z'.unop.left Z.unop.left (leOfHom k.unop.left)
      (leOfHom Z.unop.hom) a
    exact hh
@[simp] theorem localHomOfFamily_app
    (t : ∀ V : X.Opens, V ≤ U → Γ(M,V) → Γ(N,V)) hadd hsmul hres
    (Z : (Over U)ᵒᵖ) (a : Γ(M,Z.unop.left)) :
    (localHomOfFamily M N U t hadd hsmul hres).app Z a =
      t Z.unop.left (leOfHom Z.unop.hom) a := rfl

/-- A restricted module morphism read as its family of maps on honest section rings. -/
def localHomFamily
    (t : (restrFun X.sheaf.obj U).obj M.val ⟶ (restrFun X.sheaf.obj U).obj N.val)
    (V : X.Opens) (h : V ≤ U) : Γ(M,V) →ₗ[Γ(X,V)] Γ(N,V) :=
  (t.app (op (Over.mk (homOfLE h)))).hom

theorem localHomFamily_restrict
    (t : (restrFun X.sheaf.obj U).obj M.val ⟶ (restrFun X.sheaf.obj U).obj N.val)
    (V W : X.Opens) (hVW : V ≤ W) (hWU : W ≤ U) (a : Γ(M,W)) :
    localHomFamily M N U t V (hVW.trans hWU) (M.presheaf.map (homOfLE hVW).op a) =
      N.presheaf.map (homOfLE hVW).op (localHomFamily M N U t W hWU a) := by
  let k : Over.mk (homOfLE (hVW.trans hWU)) ⟶ Over.mk (homOfLE hWU) :=
    Over.homMk (homOfLE hVW) (by apply Subsingleton.elim)
  exact PresheafOfModules.naturality_apply t k.op a

end NcCubic.Geometry
