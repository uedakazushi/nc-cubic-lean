module
public import NcCubic.Geometry.SheafBiderivation
public import NcCubic.Geometry.AffineCotangentSections
@[expose] public section
noncomputable section
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R))
    (B : StructureSheafBiderivation X) (hR : B.IsRelative f)

def affineBiderivationPairing (U : X.Opens) (hU : IsAffineOpen U) :
    Γ(Scheme.Hom.relativeDifferentials f,U) →ₗ[Γ(X,U)]
      Γ(Scheme.Hom.relativeDifferentials f,U) →ₗ[Γ(X,U)] Γ(X,U) := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  let e := affineCotangentSectionsEquiv f U hU
  exact (kahlerBracket (B.linearBracket f hR U) (B.leibniz U) (B.leibniz_left U)).compl₁₂
    e.toLinearMap e.toLinearMap

theorem affineBiderivationPairing_d_d (U : X.Opens) (hU : IsAffineOpen U) (a b : Γ(X,U)) :
    affineBiderivationPairing f B hR U hU ((Scheme.Hom.universalRelativeDerivation f).d a)
      ((Scheme.Hom.universalRelativeDerivation f).d b) = B.bracket U a b := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  change kahlerBracket (B.linearBracket f hR U) (B.leibniz U) (B.leibniz_left U)
    (affineCotangentSectionsEquiv f U hU ((Scheme.Hom.universalRelativeDerivation f).d a))
    (affineCotangentSectionsEquiv f U hU ((Scheme.Hom.universalRelativeDerivation f).d b)) = _
  rw [affineCotangentSectionsEquiv_d,affineCotangentSectionsEquiv_d]
  exact kahlerBracket_d_d (B.linearBracket f hR U) (B.leibniz U) (B.leibniz_left U) a b

theorem affineBiderivationPairing_self (U : X.Opens) (hU : IsAffineOpen U)
    (a : Γ(Scheme.Hom.relativeDifferentials f,U)) : affineBiderivationPairing f B hR U hU a a=0 := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  exact kahlerBracket_alternating (B.linearBracket f hR U) (B.leibniz U) (B.leibniz_left U)
    (B.skew U) (B.self_eq_zero U) _

/-- Only on affine opens, actual differentials of functions span actual
relative cotangent sections. -/
theorem affineCotangentSections_span_d (U : X.Opens) (hU : IsAffineOpen U) :
    Submodule.span (M := Γ(Scheme.Hom.relativeDifferentials f,U)) Γ(X,U) (Set.range (fun a : Γ(X,U) => ((Scheme.Hom.universalRelativeDerivation f).d a : Γ(Scheme.Hom.relativeDifferentials f,U)))) =
      (⊤ : Submodule Γ(X,U) Γ(Scheme.Hom.relativeDifferentials f,U)) := by
  let : Algebra R Γ(X,U) := (AffineSmoothness.coefficientMap f U).toAlgebra
  let e := affineCotangentSectionsEquiv f U hU
  apply Submodule.map_injective_of_injective e.injective
  rw [Submodule.map_span,Submodule.map_top]
  have hrange : e '' Set.range (fun a : Γ(X,U) => ((Scheme.Hom.universalRelativeDerivation f).d a : Γ(Scheme.Hom.relativeDifferentials f,U))) =
      Set.range (KaehlerDifferential.D R Γ(X,U)) := by
    ext ω
    constructor
    · rintro ⟨η,⟨a,rfl⟩,hη⟩
      exact ⟨a,(affineCotangentSectionsEquiv_d f U hU a).symm.trans hη⟩
    · rintro ⟨a,rfl⟩
      exact ⟨(Scheme.Hom.universalRelativeDerivation f).d a,⟨a,rfl⟩,
        affineCotangentSectionsEquiv_d f U hU a⟩
  exact (congrArg (Submodule.span Γ(X,U)) hrange).trans
    ((KaehlerDifferential.span_range_derivation R Γ(X,U)).trans
      (LinearMap.range_eq_top.mpr e.surjective).symm)

/-- The affine pairings commute with actual restrictions; the proof uses
only spanning by actual differentials on the source affine open. -/
theorem affineBiderivationPairing_natural {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V≤U)
    (a b : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    (X.presheaf.map (homOfLE h).op) (affineBiderivationPairing f B hR U hU a b) =
      affineBiderivationPairing f B hR V hV
        ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op a)
        ((Scheme.Hom.relativeDifferentials f).presheaf.map (homOfLE h).op b) := by
  let M : X.Modules := Scheme.Hom.relativeDifferentials f
  have hmem (v : Γ(M,U)) : v ∈ Submodule.span (M:=Γ(M,U)) Γ(X,U)
      (Set.range (fun c : Γ(X,U) => ((Scheme.Hom.universalRelativeDerivation f).d c : Γ(M,U)))) := by
    rw [affineCotangentSections_span_d f U hU]
    exact Submodule.mem_top
  have hsmul (r : Γ(X,U)) (v : Γ(M,U)) :
      M.presheaf.map (homOfLE h).op (r • v) =
        (X.presheaf.map (homOfLE h).op) r • M.presheaf.map (homOfLE h).op v :=
    M.map_smul (homOfLE h) r v
  have hmd (c : Γ(X,U)) :
      M.presheaf.map (homOfLE h).op ((Scheme.Hom.universalRelativeDerivation f).d c) =
        (Scheme.Hom.universalRelativeDerivation f).d ((X.presheaf.map (homOfLE h).op) c) :=
    ((Scheme.Hom.universalRelativeDerivation f).d_map (homOfLE h).op c).symm
  have hgoal (v : Γ(M,U)) : ∀ w : Γ(M,U),
      (X.presheaf.map (homOfLE h).op) (affineBiderivationPairing f B hR U hU v w) =
        affineBiderivationPairing f B hR V hV
          (M.presheaf.map (homOfLE h).op v) (M.presheaf.map (homOfLE h).op w) := by
    induction hmem v using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨c,rfl⟩ := hv
      intro w
      induction hmem w using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨d,rfl⟩ := hw
        rw [affineBiderivationPairing_d_d,hmd,hmd,affineBiderivationPairing_d_d]
        exact B.toStructureSheafBracket.restrict h c d
      | zero => simp only [map_zero]
      | add p q _ _ hp hq => simp only [map_add,hp,hq]
      | smul r p _ hp => simp only [hsmul,map_smul,smul_eq_mul,map_mul,hp]
    | zero => intro w; simp only [map_zero,LinearMap.zero_apply]
    | add p q _ _ hp hq =>
      intro w
      simp only [map_add,LinearMap.add_apply,hp,hq]
    | smul r p _ hp =>
      intro w
      simp only [hsmul,map_smul,LinearMap.smul_apply,smul_eq_mul,map_mul,hp]
  exact hgoal a b
end NcCubic.Geometry
