module
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ExteriorPowerMono
public import NcCubic.Geometry.LineExteriorFrame
public import StacksFrontier.AlgebraicGeometry.SheafRankOne.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
universe u
namespace NcCubic.Geometry.SheafExteriorFrame
variable {X : Scheme.{u}}
local instance : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance : HasFiniteBiproducts (_root_.SheafOfModules.{u}
    (structureSheaf X.sheaf)) := HasFiniteBiproducts.of_hasFiniteProducts


abbrev tensorSquare (L : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj L).obj L

abbrev sum (L : X.Modules) (N : ℕ) : X.Modules := ⨁ (fun _ : Fin N => L)


/-- The stalk of the actual finite biproduct has its canonical coordinate
splitting; the maps are the stalks of the original projections/inclusions. -/
def stalkBiproductEquiv (L : X.Modules) (I : Type) [Fintype I] [DecidableEq I] (x : X) :
    modStalk (⨁ fun _ : I => L) x ≃ₗ[ringStalk X.sheaf x] (I → modStalk L x) where
  toFun z i := stalkHom (biproduct.π (fun _ : I => L) i) x z
  invFun v := ∑ i, stalkHom (biproduct.ι (fun _ : I => L) i) x (v i)
  map_add' z w := by ext i; exact map_add _ _ _
  map_smul' a z := by ext i; exact map_smul _ _ _
  left_inv z := by
    simpa only [AlgebraicGeometry.SheafOfModules.stalkBiproductLift,
      stalkMap_apply_eq_stalkHom] using
      AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π
        X.ringCatSheaf x (fun _ : I => L) z
  right_inv v := by
    classical
    ext j
    change stalkHom _ x (∑ i, stalkHom _ x (v i)) = v j
    rw [map_sum]
    have h : ∀ i : I,
        stalkHom (biproduct.π (fun _ : I => L) j) x
          (stalkHom (biproduct.ι (fun _ : I => L) i) x (v i)) =
          if i = j then v j else 0 := by
      intro i
      by_cases hij : i = j
      · subst i
        simpa only [stalkMap_apply_eq_stalkHom, ite_true] using
          AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_self
            X.ringCatSheaf x (fun _ : I => L) j (v j)
      · simpa only [stalkMap_apply_eq_stalkHom, ite_eq_right hij] using
          AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_ne
            X.ringCatSheaf x (fun _ : I => L) hij (v i)
    simp_rw [h]
    simp

@[simp] theorem stalkBiproductEquiv_symm_single (L : X.Modules) (I : Type) [Fintype I] [DecidableEq I] (x : X)
    (i : I) (v : modStalk L x) :
    (stalkBiproductEquiv L I x).symm (Pi.single i v) =
      stalkHom (biproduct.ι (fun _ : I => L) i) x v := by
  classical
  change (∑ j, stalkHom (biproduct.ι (fun _ : I => L) j) x ((Pi.single i v : I → modStalk L x) j)) = _
  simp [Pi.single_apply, apply_ite]

@[simp] theorem stalkBiproductEquiv_inclusion (L : X.Modules) (I : Type) [Fintype I] [DecidableEq I] (x : X)
    (i : I) (v : modStalk L x) :
    stalkBiproductEquiv L I x (stalkHom (biproduct.ι (fun _ : I => L) i) x v) =
      Pi.single i v := by
  rw [← stalkBiproductEquiv_symm_single, LinearEquiv.apply_symm_apply]

abbrev stalkSumEquiv (L : X.Modules) (N : ℕ) (x : X) :=
  stalkBiproductEquiv L (Fin N) x

/-- A rank-one bundle gives a line trivialization at every actual stalk. -/
theorem nonempty_stalkLineEquiv (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1) (x : X) :
    Nonempty (modStalk L x ≃ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x) := by
  obtain ⟨q, hq, hr⟩ := hL.exists_isFiniteLocallyFreeOfRankData
  have := hq
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ q.X).1 q.coversTop).exists_mem x
  obtain ⟨b⟩ := Stacks.StalkFreeBridge.nonempty_stalkBasis_of_isLocallyFreeData L q i hi
  obtain ⟨e⟩ := hr i
  let b' : Module.Basis (Fin 1) (ringStalk X.sheaf x) (modStalk L x) := b.reindex e
  exact ⟨b'.equivFun.trans (LinearEquiv.funUnique (Fin 1)
    (↑(ringStalk X.sheaf x)) (↑(ringStalk X.sheaf x)))⟩

/-- Canonical ordered coordinate wedge, without choosing a trivialization of L. -/
def component (L : X.Modules) (N : ℕ) (i j : Fin N) :
    tensorSquare L ⟶ Scheme.Modules.exteriorPower (sum L N) 2 :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map
    (biproduct.ι (fun _ : Fin N => L) i ≫ Scheme.Modules.exteriorGenerator (sum L N))).app L ≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj _).map
      (biproduct.ι (fun _ : Fin N => L) j ≫ Scheme.Modules.exteriorGenerator (sum L N))) ≫
    SheafOfModules.GradedAlgebra.mulSheaf (Scheme.Modules.exteriorAlgebra (sum L N)) 1 1

/-- Canonical reconstruction from ordered pairs of coordinate lines. -/
def reconstruction (L : X.Modules) (N : ℕ) :
    (⨁ fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) ⟶
      Scheme.Modules.exteriorPower (sum L N) 2 :=
  biproduct.desc fun s => component L N
    (Set.powersetCard.ofFinEmbEquiv.symm s 0) (Set.powersetCard.ofFinEmbEquiv.symm s 1)

@[simp] theorem inclusion_reconstruction (L : X.Modules) (N : ℕ)
    (s : Set.powersetCard (Fin N) 2) :
    biproduct.ι (fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) s ≫
      reconstruction L N = component L N
        (Set.powersetCard.ofFinEmbEquiv.symm s 0) (Set.powersetCard.ofFinEmbEquiv.symm s 1) := by
  simp [reconstruction]

/-- The ordered-pair component on actual local pure tensors. -/
theorem component_tensor (L : X.Modules) (N : ℕ) (i j : Fin N)
    (U : X.Opensᵒᵖ) (v w : L.val.obj U) :
    (component L N i j).val.app U
      ((PresheafOfModules.tensorSheafUnit L L).app U (v ⊗ₜ w)) =
    ((Scheme.Modules.exteriorAlgebra (sum L N)).toPresheafGradedAlgebra.mul 1 1).app U
      ((Scheme.Modules.exteriorGenerator (sum L N)).val.app U
        ((biproduct.ι (fun _ : Fin N => L) i).val.app U v))
      ((Scheme.Modules.exteriorGenerator (sum L N)).val.app U
        ((biproduct.ι (fun _ : Fin N => L) j).val.app U w)) := by
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    X.sheaf L L
    (biproduct.ι (fun _ : Fin N => L) i ≫ Scheme.Modules.exteriorGenerator (sum L N))
    (biproduct.ι (fun _ : Fin N => L) j ≫ Scheme.Modules.exteriorGenerator (sum L N)) U v w
  unfold component
  change (SheafOfModules.GradedAlgebra.mulSheaf
    (Scheme.Modules.exteriorAlgebra (sum L N)) 1 1).val.app U _ = _
  erw [h]
  exact SheafOfModules.GradedAlgebra.mulSheaf_unit _ 1 1 U _ _

/-- Ordered products of two generators are the corresponding local wedge. -/
theorem component_wedge (L : X.Modules) (N : ℕ) (i j : Fin N)
    (U : X.Opensᵒᵖ) (v w : L.val.obj U) :
    (component L N i j).val.app U
      ((PresheafOfModules.tensorSheafUnit L L).app U (v ⊗ₜ w)) =
    (Scheme.Modules.exteriorAlgebra (sum L N)).toPresheafGradedAlgebra.homogeneousProd U 2
      ![(Scheme.Modules.exteriorGenerator (sum L N)).val.app U
        ((biproduct.ι (fun _ : Fin N => L) i).val.app U v),
      (Scheme.Modules.exteriorGenerator (sum L N)).val.app U
        ((biproduct.ι (fun _ : Fin N => L) j).val.app U w)] := by
  rw [component_tensor]
  let A := (Scheme.Modules.exteriorAlgebra (sum L N)).toPresheafGradedAlgebra
  have h1 (z : Fin 1 → ((sum L N).exteriorAlgebra.piece 1).val.obj U) :
      A.homogeneousProd U 1 z = z 0 := eq_of_heq (A.one_mul 1 U (z 0))
  change _ = (A.mul 1 1).app U (A.homogeneousProd U 1 _) _
  rw [h1]
  rfl

abbrev exteriorStalkEquiv (L : X.Modules) (N : ℕ) (x : X) :=
  (_root_.SheafOfModules.algebras _ (sum L N)).exteriorPowerStalkEquiv 2 x

/-- The canonical coordinate wedge has the expected actual stalk value. -/
theorem component_stalk_germ (L : X.Modules) (N : ℕ) (i j : Fin N)
    (x : X) (U : X.Opens) (hx : x ∈ U) (v w : L.val.obj (.op U)) :
    exteriorStalkEquiv L N x
      (stalkHom (component L N i j) x
        (PresheafOfModules.tensorSheafGerm X.sheaf L L x U hx v w)) =
      exteriorPower.ιMulti (ringStalk X.sheaf x) 2
        ![stalkHom (biproduct.ι (fun _ : Fin N => L) i) x
          (TopCat.Presheaf.germ L.val.presheaf U x hx v),
        stalkHom (biproduct.ι (fun _ : Fin N => L) j) x
          (TopCat.Presheaf.germ L.val.presheaf U x hx w)] := by
  have hg := stalkHom_germAt (component L N i j) x U hx
    ((PresheafOfModules.tensorSheafUnit L L).app (.op U) (v ⊗ₜ w))
  have hw := component_wedge L N i j (.op U) v w
  have hgw := hg.trans (congrArg
    (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower (sum L N) 2).val.presheaf U x hx) hw)
  refine (congrArg (exteriorStalkEquiv L N x) hgw).trans ?_
  have hh := _root_.SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd
    (Scheme.Modules.exteriorAlgebra (sum L N))
    (Scheme.Modules.exteriorGenerator (sum L N))
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra (sum L N)) 2 x U hx
    ![(biproduct.ι (fun _ : Fin N => L) i).val.app (.op U) v,
      (biproduct.ι (fun _ : Fin N => L) j).val.app (.op U) w]
  refine hh.trans ?_
  congr 1
  funext k
  fin_cases k
  · exact (stalkHom_germAt (biproduct.ι (fun _ : Fin N => L) i) x U hx v).symm
  · exact (stalkHom_germAt (biproduct.ι (fun _ : Fin N => L) j) x U hx w).symm

/-- The ordered coordinate-wedge formula holds for all stalk tensors, not
only for sections over one chosen open neighbourhood. -/
theorem component_stalk_tmul (L : X.Modules) (N : ℕ) (i j : Fin N)
    (x : X) (v w : modStalk L x) :
    exteriorStalkEquiv L N x
      (stalkHom (component L N i j) x
        ((PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).symm (v ⊗ₜ w))) =
      exteriorPower.ιMulti (ringStalk X.sheaf x) 2
        ![stalkHom (biproduct.ι (fun _ : Fin N => L) i) x v,
        stalkHom (biproduct.ι (fun _ : Fin N => L) j) x w] := by
  obtain ⟨U, hx, s, hs⟩ := _root_.SheafOfModules.exists_germ_eq_family L x 2 ![v,w]
  have hs0 : TopCat.Presheaf.germ L.val.presheaf U x hx (s 0) = v := hs 0
  have hs1 : TopCat.Presheaf.germ L.val.presheaf U x hx (s 1) = w := hs 1
  have hg := PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm
    X.sheaf L L x U hx (s 0) (s 1)
  have ht : (PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).symm (v ⊗ₜ w) =
      PresheafOfModules.tensorSheafGerm X.sheaf L L x U hx (s 0) (s 1) :=
    (LinearEquiv.symm_apply_eq _).2
      (hg.trans (congrArg₂ (fun a b => a ⊗ₜ b) hs0 hs1)).symm
  have hh := component_stalk_germ L N i j x U hx (s 0) (s 1)
  exact (congrArg (fun z => exteriorStalkEquiv L N x
    (stalkHom (component L N i j) x z)) ht).trans
    (hh.trans (congrArg₂ (fun a b => exteriorPower.ιMulti (ringStalk X.sheaf x) 2
      ![stalkHom (biproduct.ι (fun _ : Fin N => L) i) x a,
        stalkHom (biproduct.ι (fun _ : Fin N => L) j) x b]) hs0 hs1))

/-- Scalar coordinates for the source on a trivialized stalk; this is used
only to verify the intrinsically defined reconstruction morphism. -/
def sourceCoordinateEquiv (L : X.Modules) (N : ℕ) (x : X)
    (e : modStalk L x ≃ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x) :=
  (stalkBiproductEquiv (tensorSquare L) (Set.powersetCard (Fin N) 2) x).trans
    (LinearEquiv.piCongrRight fun _ =>
      (PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).trans
        (LineExteriorFrame.tensorCoordinate e))

/-- Scalar exterior-basis coordinates on the target stalk. -/
def targetCoordinateEquiv (L : X.Modules) (N : ℕ) (x : X)
    (e : modStalk L x ≃ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x) :=
  (exteriorStalkEquiv L N x).trans
    ((exteriorPowerCongr 2 (stalkSumEquiv L N x)).trans
      ((LineExteriorFrame.sumBasis e N).exteriorPower 2).equivFun)

theorem sourceCoordinateEquiv_symm_single (L : X.Modules) (N : ℕ) (x : X)
    (e : modStalk L x ≃ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x)
    (s : Set.powersetCard (Fin N) 2) :
    (sourceCoordinateEquiv L N x e).symm (Pi.single s 1) =
      stalkHom (biproduct.ι (fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) s) x
        ((PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).symm
          (e.symm 1 ⊗ₜ e.symm 1)) := by
  have hs : ((LinearEquiv.piCongrRight fun _ : Set.powersetCard (Fin N) 2 =>
      (PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).trans
        (LineExteriorFrame.tensorCoordinate e)).symm (Pi.single s 1)) =
      Pi.single s ((PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).symm
        (e.symm 1 ⊗ₜ e.symm 1)) := by
    ext t
    by_cases h : t = s
    · subst t; simp [LineExteriorFrame.tensorCoordinate_symm_one]
    · simp [LinearEquiv.piCongrRight_symm, h]
  change (stalkBiproductEquiv (tensorSquare L) _ x).symm _ = _
  exact (congrArg (stalkBiproductEquiv (tensorSquare L) _ x).symm hs).trans
    (stalkBiproductEquiv_symm_single _ _ _ _ _)

theorem targetCoordinateEquiv_component (L : X.Modules) (N : ℕ) (x : X)
    (e : modStalk L x ≃ₗ[ringStalk X.sheaf x] ringStalk X.sheaf x)
    (s : Set.powersetCard (Fin N) 2) :
    targetCoordinateEquiv L N x e
      (stalkHom (component L N
        (Set.powersetCard.ofFinEmbEquiv.symm s 0)
        (Set.powersetCard.ofFinEmbEquiv.symm s 1)) x
        ((PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).symm
          (e.symm 1 ⊗ₜ e.symm 1))) = Pi.single s 1 := by
  unfold targetCoordinateEquiv
  change ((LineExteriorFrame.sumBasis e N).exteriorPower 2).equivFun
    (exteriorPowerCongr 2 (stalkSumEquiv L N x)
      (exteriorStalkEquiv L N x _)) = _
  rw [component_stalk_tmul, Stacks.exteriorPowerCongr_ιMulti]
  have hv : (fun k : Fin 2 => stalkSumEquiv L N x
      (![stalkHom (biproduct.ι (fun _ : Fin N => L)
          (Set.powersetCard.ofFinEmbEquiv.symm s 0)) x (e.symm 1),
        stalkHom (biproduct.ι (fun _ : Fin N => L)
          (Set.powersetCard.ofFinEmbEquiv.symm s 1)) x (e.symm 1)] k)) =
      (fun k => LineExteriorFrame.sumBasis e N
        (Set.powersetCard.ofFinEmbEquiv.symm s k)) := by
    funext k
    fin_cases k <;> simp [stalkSumEquiv]
  rw [hv]
  change ((LineExteriorFrame.sumBasis e N).exteriorPower 2).equivFun
    (exteriorPower.ιMulti_family _ 2 (LineExteriorFrame.sumBasis e N) s) = _
  rw [← exteriorPower.basis_apply]
  ext t
  simp only [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]

/-- The canonical reconstruction is an isomorphism for an actual rank-one
bundle; its stalk matrix in the explicit coordinate frames is the identity. -/
theorem isIso_reconstruction (L : X.Modules) (N : ℕ)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1) :
    IsIso (reconstruction L N) := by
  apply isIso_of_bijective_stalkHom
  intro x
  obtain ⟨e⟩ := nonempty_stalkLineEquiv L hL x
  let eS := sourceCoordinateEquiv L N x e
  let eT := targetCoordinateEquiv L N x e
  have hm : eT.toLinearMap ∘ₗ (stalkHom (reconstruction L N) x ∘ₗ eS.symm.toLinearMap) =
      LinearMap.id := by
    apply (Pi.basisFun (↑(ringStalk X.sheaf x)) (Set.powersetCard (Fin N) 2)).ext
    intro s
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe]
    change eT (stalkHom (reconstruction L N) x (eS.symm (Pi.single s 1))) = Pi.single s 1
    change targetCoordinateEquiv L N x e
      (stalkHom (reconstruction L N) x ((sourceCoordinateEquiv L N x e).symm _)) = _
    rw [sourceCoordinateEquiv_symm_single]
    have hc := congrArg (fun f => stalkHom f x) (inclusion_reconstruction L N s)
    rw [stalkHom_comp] at hc
    have hc' := LinearMap.congr_fun hc
      ((PresheafOfModules.tensorSheafStalkEquiv X.sheaf L L x).symm
        (e.symm 1 ⊗ₜ e.symm 1))
    change targetCoordinateEquiv L N x e _ = _
    rw [← LinearMap.comp_apply, hc']
    exact targetCoordinateEquiv_component L N x e s
  have hformula : stalkHom (reconstruction L N) x =
      eT.symm.toLinearMap ∘ₗ eS.toLinearMap := by
    ext z
    apply eT.injective
    change eT (stalkHom (reconstruction L N) x z) = eT (eT.symm (eS z))
    rw [LinearEquiv.apply_symm_apply]
    have hh := LinearMap.congr_fun hm (eS z)
    change eT (stalkHom (reconstruction L N) x (eS.symm (eS z))) = eS z at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    exact hh

  rw [hformula]
  exact eT.symm.bijective.comp eS.bijective

/-- The canonical coordinate decomposition, with reconstruction given by
ordered coordinate wedges rather than a dimension-counting object isomorphism. -/
def coordinateIso (L : X.Modules) (N : ℕ)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1) :
    (⨁ fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) ≅
      Scheme.Modules.exteriorPower (sum L N) 2 :=
  @asIso _ _ _ _ (reconstruction L N) (isIso_reconstruction L N hL)

@[simp] theorem coordinateIso_hom (L : X.Modules) (N : ℕ)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1) :
    (coordinateIso L N hL).hom = reconstruction L N := rfl

/-- The same conclusion phrased directly for an invertible sheaf. -/
theorem isIso_reconstruction_of_invertible (L : X.Modules) (N : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    IsIso (reconstruction L N) :=
  isIso_reconstruction L N
    (Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L)

/-- Projection to one actual tensor-square coordinate. -/
def projection (L : X.Modules) (N : ℕ)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1)
    (s : Set.powersetCard (Fin N) 2) :
    Scheme.Modules.exteriorPower (sum L N) 2 ⟶ tensorSquare L :=
  (coordinateIso L N hL).inv ≫
    biproduct.π (fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) s

@[simp] theorem reconstruction_projection (L : X.Modules) (N : ℕ)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1)
    (s : Set.powersetCard (Fin N) 2) :
    reconstruction L N ≫ projection L N hL s =
      biproduct.π (fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) s := by
  change (coordinateIso L N hL).hom ≫ ((coordinateIso L N hL).inv ≫ _) = _
  exact Iso.hom_inv_id_assoc _ _

@[simp] theorem component_projection (L : X.Modules) (N : ℕ)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1)
    (s t : Set.powersetCard (Fin N) 2) :
    component L N (Set.powersetCard.ofFinEmbEquiv.symm s 0)
      (Set.powersetCard.ofFinEmbEquiv.symm s 1) ≫ projection L N hL t =
      if s = t then 𝟙 (tensorSquare L) else 0 := by
  rw [← inclusion_reconstruction L N s]
  change (biproduct.ι (fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) s ≫
    (coordinateIso L N hL).hom) ≫ ((coordinateIso L N hL).inv ≫ _) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact biproduct.ι_π _ _ _

/-- Every bivector is reconstructed from the canonical pair coordinates. -/
theorem projections_reconstruct (L : X.Modules) (N : ℕ)
    (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1) :
    ∑ s : Set.powersetCard (Fin N) 2,
      projection L N hL s ≫ component L N
        (Set.powersetCard.ofFinEmbEquiv.symm s 0)
        (Set.powersetCard.ofFinEmbEquiv.symm s 1) = 𝟙 _ := by
  have h := congrArg (fun f => (coordinateIso L N hL).inv ≫ f ≫
    (coordinateIso L N hL).hom)
    (biproduct.total (f := fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L))
  have hι (s : Set.powersetCard (Fin N) 2) :
      biproduct.ι (fun _ : Set.powersetCard (Fin N) 2 => tensorSquare L) s ≫
        (coordinateIso L N hL).hom = component L N
          (Set.powersetCard.ofFinEmbEquiv.symm s 0)
          (Set.powersetCard.ofFinEmbEquiv.symm s 1) := inclusion_reconstruction L N s
  simpa only [projection, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
    Category.id_comp, Category.comp_id, Iso.inv_hom_id, hι] using h

end NcCubic.Geometry.SheafExteriorFrame
