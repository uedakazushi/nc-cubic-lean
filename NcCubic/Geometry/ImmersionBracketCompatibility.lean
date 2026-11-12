/- Actual bivector brackets commute with an actual pullback extension.
Only explicit determinant laws for genuine pairings remain as generic inputs. -/
module
public import NcCubic.Geometry.ImmersionPairingCompatibility
public import NcCubic.Geometry.DeterminantBracketAgreement
@[expose] public section
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
universe u
namespace NcCubic.Geometry.ImmersionBracketNaturality
open ImmersionBivector
lemma cotangentWedge_pullback {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (U : P.Opens) (a b : Γ(P,U)) :
    (Scheme.Modules.exteriorPowerMap (cotangentMap i p) (2:ℤ)).val.app (op (i ⁻¹ᵁ U))
      ((exteriorPullbackIso i (Scheme.Hom.relativeDifferentials p) (2:ℤ)).hom.val.app (op (i ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (exteriorSquare P (Scheme.Hom.relativeDifferentials p))).val.app (op U)
          (exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials p) U
            ![(Scheme.Hom.universalRelativeDerivation p).d a,(Scheme.Hom.universalRelativeDerivation p).d b]))) =
    exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials (i ≫ p)) (i ⁻¹ᵁ U)
      ![(Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U).hom a),
        (Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U).hom b)] := by
  let M := Scheme.Hom.relativeDifferentials p
  let N := Scheme.Hom.relativeDifferentials (i ≫ p)
  let W := i ⁻¹ᵁ U
  let v : Fin 2 → Γ(M,U) :=
    ![(Scheme.Hom.universalRelativeDerivation p).d a,(Scheme.Hom.universalRelativeDerivation p).d b]
  let w : Fin 2 → Γ((Scheme.Modules.pullback i).obj M,W) := fun j =>
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U) (v j))
  have hp := exteriorPullbackIso_unit_wedge i M U v
  have hm := exteriorWedgeAlternating_map (cotangentMap i p) W w
  have hv : (fun j => (cotangentMap i p).val.app (op W) (w j)) =
      ![(Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U).hom a),
        (Scheme.Hom.universalRelativeDerivation (i ≫ p)).d ((i.app U).hom b)] := by
    funext j
    fin_cases j
    · exact cotangentMap_unit_differentials i p U a
    · exact cotangentMap_unit_differentials i p U b
  exact (congrArg ((Scheme.Modules.exteriorPowerMap (cotangentMap i p) (2:ℤ)).val.app (op W)) hp).trans
    (hm.trans (congrArg (exteriorWedgeAlternating N W) hv))

lemma bivectorSectionBracket_pullback_of_determinantFormulas
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (qP : exteriorSquareTensor P (dualSheaf (Scheme.Hom.relativeDifferentials p))
      (Scheme.Hom.relativeDifferentials p) ⟶ SheafOfModules.unit P.ringCatSheaf)
    (qB : exteriorSquareTensor X (dualSheaf ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)))
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (qX : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p)))
      (Scheme.Hom.relativeDifferentials (i ≫ p)) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hP : HasDeterminantFormula (Scheme.Hom.relativeDifferentials p) qP)
    (hB : HasDeterminantFormula ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) qB)
    (hX : HasDeterminantFormula (Scheme.Hom.relativeDifferentials (i ≫ p)) qX)
    (U : P.Opens) (piP : Γ(bivectorSheaf p,U)) (piX : Γ(bivectorSheaf (i ≫ p),i ⁻¹ᵁ U))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op U) piP) =
      (bivectorMap i p hΩ).val.app (op (i ⁻¹ᵁ U)) piX)
    (a b : Γ(P,U)) :
    (i.app U).hom (bivectorSectionBracket p U piP a b) =
      bivectorSectionBracket (i ≫ p) (i ⁻¹ᵁ U) piX ((i.app U).hom a) ((i.app U).hom b) := by
  have htau : tangentMap i p hΩ ≫ PullbackDual.pullbackDualMap i (Scheme.Hom.relativeDifferentials p) =
      dualMap (cotangentMap i p) := tangentMap_comp_dualComparison i p hΩ
  have hs := determinant_evaluation_of_extension i (Scheme.Hom.relativeDifferentials p)
    (Scheme.Hom.relativeDifferentials (i ≫ p)) (cotangentMap i p) (tangentMap i p hΩ) htau
    qP qB qX hP hB hX U piP piX hext
    (exteriorWedgeAlternating (Scheme.Hom.relativeDifferentials p) U
      ![(Scheme.Hom.universalRelativeDerivation p).d a,(Scheme.Hom.universalRelativeDerivation p).d b])
  have hf := congrArg (fun z => qX.val.app (op (i ⁻¹ᵁ U))
    (PullbackDual.tensorSheafPure X _ _ (i ⁻¹ᵁ U)
      (piX ⊗ₜ[X.presheaf.obj (op (i ⁻¹ᵁ U))] z))) (cotangentWedge_pullback i p U a b)
  exact (congrArg (i.app U).hom (determinantPairing_bracket p qP hP U piP a b)).symm.trans
    (hs.trans (hf.trans (determinantPairing_bracket (i ≫ p) qX hX (i ⁻¹ᵁ U) piX
      ((i.app U).hom a) ((i.app U).hom b))))
lemma extension_restrict {X P : Scheme.{u}} (i : X ⟶ P) (M : P.Modules) (E : X.Modules)
    (tau : E ⟶ (Scheme.Modules.pullback i).obj M) (s : Γ(M,⊤)) (t : Γ(E,⊤))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op ⊤) s) =
      tau.val.app (op ⊤) t) (U : P.Opens) :
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val.app (op U)
      (M.presheaf.map (homOfLE (show U≤⊤ from le_top)).op s)) =
      tau.val.app (op (i ⁻¹ᵁ U))
        (E.presheaf.map (homOfLE (show i ⁻¹ᵁ U≤⊤ from le_top)).op t) := by
  have hu := PresheafOfModules.naturality_apply
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).val)
    (homOfLE (show U≤⊤ from le_top)).op s
  have ht := PresheafOfModules.naturality_apply tau.val
    (homOfLE (show i ⁻¹ᵁ U≤⊤ from le_top)).op t
  exact hu.trans ((congrArg (((Scheme.Modules.pullback i).obj M).val.map
    (homOfLE (show i ⁻¹ᵁ U≤⊤ from le_top)).op) hext).trans ht.symm)

lemma algebraicBivectorBracket_pullback_of_determinantFormulas
    {X P S : Scheme.{u}} (i : X ⟶ P) (p : P ⟶ S)
    (hΩ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Hom.relativeDifferentials p))
    (qP : exteriorSquareTensor P (dualSheaf (Scheme.Hom.relativeDifferentials p))
      (Scheme.Hom.relativeDifferentials p) ⟶ SheafOfModules.unit P.ringCatSheaf)
    (qB : exteriorSquareTensor X (dualSheaf ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)))
      ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (qX : exteriorSquareTensor X (dualSheaf (Scheme.Hom.relativeDifferentials (i ≫ p)))
      (Scheme.Hom.relativeDifferentials (i ≫ p)) ⟶ SheafOfModules.unit X.ringCatSheaf)
    (hP : HasDeterminantFormula (Scheme.Hom.relativeDifferentials p) qP)
    (hB : HasDeterminantFormula ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) qB)
    (hX : HasDeterminantFormula (Scheme.Hom.relativeDifferentials (i ≫ p)) qX)
    (piP : AlgebraicBivector p) (piX : AlgebraicBivector (i ≫ p))
    (hext : (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (bivectorSheaf p)).val.app (op ⊤) piP) =
      (bivectorMap i p hΩ).val.app (op ⊤) piX)
    (U : P.Opens) (a b : Γ(P,U)) :
    (i.app U).hom ((algebraicBivectorBracket p piP).bracket U a b) =
      (algebraicBivectorBracket (i ≫ p) piX).bracket (i ⁻¹ᵁ U) ((i.app U).hom a) ((i.app U).hom b) := by
  have hU := extension_restrict i (bivectorSheaf p) (bivectorSheaf (i ≫ p))
    (bivectorMap i p hΩ) piP piX hext U
  have hlocal := bivectorSectionBracket_pullback_of_determinantFormulas i p hΩ qP qB qX hP hB hX U
    ((bivectorSheaf p).presheaf.map (homOfLE (show U≤⊤ from le_top)).op piP)
    ((bivectorSheaf (i ≫ p)).presheaf.map (homOfLE (show i ⁻¹ᵁ U≤⊤ from le_top)).op piX) hU a b
  exact (congrArg (i.app U).hom (algebraicBivectorBracket_eq_sectionBracket p piP U a b)).trans
    (hlocal.trans (algebraicBivectorBracket_eq_sectionBracket (i ≫ p) piX (i ⁻¹ᵁ U)
      ((i.app U).hom a) ((i.app U).hom b)).symm)
end NcCubic.Geometry.ImmersionBracketNaturality
