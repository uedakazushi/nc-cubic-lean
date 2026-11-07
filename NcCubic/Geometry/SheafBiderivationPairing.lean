module
public import NcCubic.Geometry.AffineBiderivationPairing
public import NcCubic.Geometry.BasisModulePairingGluing
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (B : StructureSheafBiderivation X) (hR : B.IsRelative f)

theorem affineOpenBasis_cover (U : X.Opens) :
    U ≤ ⨆ V : {V : X.affineOpens // V.val ≤ U},V.val.val := by
  intro x hx
  obtain ⟨_,⟨V,hV,rfl⟩,hxV,hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V,hV⟩,hVU⟩,hxV⟩

private theorem pairing_ring_res_comp {U V T : X.Opens} (h : T≤V) (k : V≤U) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op) ((X.presheaf.map (homOfLE k).op) a) =
      (X.presheaf.map (homOfLE (h.trans k)).op) a := by
  rw [← ConcreteCategory.comp_apply,← X.presheaf.map_comp]
  rfl
private theorem pairing_module_res_comp (M : X.Modules) {U V T : X.Opens}
    (h : T≤V) (k : V≤U) (a : Γ(M,U)) :
    (M.presheaf.map (homOfLE h).op) ((M.presheaf.map (homOfLE k).op) a) =
      (M.presheaf.map (homOfLE (h.trans k)).op) a := by
  rw [← ConcreteCategory.comp_apply,← M.presheaf.map_comp]
  rfl

def biderivationBasisPairing :
    BasisModulePairingData X (Scheme.Hom.relativeDifferentials f) (fun U : X.affineOpens => U.val) where
  cover := affineOpenBasis_cover
  pair U := affineBiderivationPairing f B hR U.val U.property
  overlap U V a b c d ha hb := by
    apply X.sheaf.eq_of_locally_eq' (fun W : {W : X.affineOpens // W.val ≤ U.val ⊓ V.val} => W.val.val)
      (U.val ⊓ V.val) (fun W => homOfLE W.property) (affineOpenBasis_cover (U.val ⊓ V.val))
    intro W
    have haW := congrArg (fun z => (Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE W.property).op z) ha
    have hbW := congrArg (fun z => (Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE W.property).op z) hb
    simp only [pairing_module_res_comp] at haW hbW
    have h1 := affineBiderivationPairing_natural f B hR U.property W.val.property
      (W.property.trans inf_le_left) a b
    have h2 := affineBiderivationPairing_natural f B hR V.property W.val.property
      (W.property.trans inf_le_right) c d
    exact (pairing_ring_res_comp W.property inf_le_left _).trans
      ((h1.trans ((congrArg₂ (fun x y : Γ(Scheme.Hom.relativeDifferentials f,W.val.val) =>
          affineBiderivationPairing f B hR W.val.val W.val.property x y) haW hbW).trans h2.symm)).trans (pairing_ring_res_comp W.property inf_le_right _).symm)

/-- The genuine all-open cotangent pairing associated to a relative
structure-sheaf biderivation. Only affine-open comparisons entered its construction. -/
def biderivationAlternating (U : X.Opens) :
    AlternatingMap Γ(X,U) Γ(Scheme.Hom.relativeDifferentials f,U) Γ(X,U) (Fin 2) :=
  (biderivationBasisPairing f B hR).gluedAlternating
    (fun U a => affineBiderivationPairing_self f B hR U.val U.property a) U

theorem biderivationAlternating_natural {U V : X.Opens} (h : V≤U)
    (v : Fin 2 → Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (X.presheaf.map (homOfLE h).op) (biderivationAlternating f B hR U v) =
      biderivationAlternating f B hR V
        (fun i => (Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op (v i)) :=
  (biderivationBasisPairing f B hR).gluedAlternating_natural _ h v

theorem biderivationAlternating_d_d (U : X.Opens) (a b : Γ(X,U)) :
    biderivationAlternating f B hR U
      ![(Scheme.Hom.universalRelativeDerivation f).d a,(Scheme.Hom.universalRelativeDerivation f).d b] =
      B.bracket U a b := by
  apply (biderivationBasisPairing f B hR).eq_of_basis
  intro V hV
  change (X.presheaf.map (homOfLE hV).op)
    ((biderivationBasisPairing f B hR).gluedPair U
      ((Scheme.Hom.universalRelativeDerivation f).d a) ((Scheme.Hom.universalRelativeDerivation f).d b)) = _
  apply ((biderivationBasisPairing f B hR).gluedPair_restrict U
    ((Scheme.Hom.universalRelativeDerivation f).d a) ((Scheme.Hom.universalRelativeDerivation f).d b) V hV).trans
  have hmd (c : Γ(X,U)) :
      (Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE hV).op
        ((Scheme.Hom.universalRelativeDerivation f).d c) =
      (Scheme.Hom.universalRelativeDerivation f).d ((X.presheaf.map (homOfLE hV).op) c) :=
    ((Scheme.Hom.universalRelativeDerivation f).d_map (homOfLE hV).op c).symm
  change affineBiderivationPairing f B hR V.val V.property _ _ = _
  rw [hmd,hmd]
  exact (affineBiderivationPairing_d_d f B hR V.val V.property _ _).trans
    (B.toStructureSheafBracket.restrict hV a b).symm
end NcCubic.Geometry
