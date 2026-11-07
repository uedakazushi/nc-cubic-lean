module
public import NcCubic.Geometry.BivectorEvaluation
public import NcCubic.Geometry.TwistSumSections
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace NcCubic.Geometry
universe u v w

/-- Evaluation of a section of an internal Hom is linear in that section.
The abstract presheaf statement avoids concrete scheme-section carrier conversions. -/
def internalHomEvaluateAtLinear {C : Type u} [Category.{v} C]
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G : PresheafOfModules.{w} (Oforget O)) (U : C) (x : F.obj (op U)) :
    (internalHom O F G).obj (op U) →ₗ[(Oforget O).obj (op U)] G.obj (op U) where
  toFun α := (α.app (op (Over.mk (𝟙 U)))).hom x
  map_add' α β := rfl
  map_smul' c α := by
    change ((smulHom O F G U c α).app (op (Over.mk (𝟙 U)))).hom x = _
    change (fRestr O U c (op (Over.mk (𝟙 U)))) •
      ((α.app (op (Over.mk (𝟙 U)))).hom x) = c • _
    change (((Oforget O).map (𝟙 (op U))).hom c) • _ = c • _
    rw [(Oforget O).map_id]
    rfl

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The actual cotangent-to-tangent evaluation, linear in the contraction section. -/
def contractionEvaluateAtLinear (U : X.Opens)
    (a : Γ(Scheme.Hom.relativeDifferentials f,U)) :
    Γ(tangentContractionSheaf f,U) →ₗ[Γ(X,U)] Γ(tangentSheaf f,U) :=
  internalHomEvaluateAtLinear X.sheaf.obj (Scheme.Hom.relativeDifferentials f).val
    (tangentSheaf f).val U a

@[simp] theorem contractionEvaluateAtLinear_apply (U : X.Opens)
    (a : Γ(Scheme.Hom.relativeDifferentials f,U)) (c : Γ(tangentContractionSheaf f,U)) :
    contractionEvaluateAtLinear f U a c = contractionEvaluation f U c a := rfl

/-- Evaluation on two functions is linear in the actual contraction section. -/
def contractionSectionBracketLinear (U : X.Opens) (a b : Γ(X,U)) :
    Γ(tangentContractionSheaf f,U) →ₗ[Γ(X,U)] Γ(X,U) :=
  (LinearMap.applyₗ (R := Γ(X,U)) (M₂ := Γ(X,U))
    ((Scheme.Hom.universalRelativeDerivation f).d b)).comp
    ((tangentEvaluationLinear f U).comp
      (contractionEvaluateAtLinear f U ((Scheme.Hom.universalRelativeDerivation f).d a)))

@[simp] theorem contractionSectionBracketLinear_apply (U : X.Opens) (a b : Γ(X,U))
    (c : Γ(tangentContractionSheaf f,U)) :
    contractionSectionBracketLinear f U a b c = contractionSectionBracket f U c a b := rfl

/-- The actual local bivector bracket is linear in the bivector section. -/
def bivectorSectionBracketLinear (U : X.Opens) (a b : Γ(X,U)) :
    Γ(bivectorSheaf f,U) →ₗ[Γ(X,U)] Γ(X,U) :=
  (contractionSectionBracketLinear f U a b).comp
    ((bivectorContraction f).val.app (op U)).hom

@[simp] theorem bivectorSectionBracketLinear_apply (U : X.Opens) (a b : Γ(X,U))
    (π : Γ(bivectorSheaf f,U)) :
    bivectorSectionBracketLinear f U a b π = bivectorSectionBracket f U π a b := rfl

@[simp] theorem bivectorSectionBracket_zero (U : X.Opens) (a b : Γ(X,U)) :
    bivectorSectionBracket f U 0 a b = 0 :=
  (bivectorSectionBracketLinear f U a b).map_zero

theorem bivectorSectionBracket_add (U : X.Opens) (π τ : Γ(bivectorSheaf f,U))
    (a b : Γ(X,U)) :
    bivectorSectionBracket f U (π + τ) a b =
      bivectorSectionBracket f U π a b + bivectorSectionBracket f U τ a b :=
  (bivectorSectionBracketLinear f U a b).map_add π τ

theorem bivectorSectionBracket_sub (U : X.Opens) (π τ : Γ(bivectorSheaf f,U))
    (a b : Γ(X,U)) :
    bivectorSectionBracket f U (π - τ) a b =
      bivectorSectionBracket f U π a b - bivectorSectionBracket f U τ a b :=
  (bivectorSectionBracketLinear f U a b).map_sub π τ

@[simp] theorem bivectorSectionBracket_neg (U : X.Opens) (π : Γ(bivectorSheaf f,U))
    (a b : Γ(X,U)) :
    bivectorSectionBracket f U (-π) a b = -bivectorSectionBracket f U π a b :=
  (bivectorSectionBracketLinear f U a b).map_neg π

theorem bivectorSectionBracket_smul (U : X.Opens) (r : Γ(X,U))
    (π : Γ(bivectorSheaf f,U)) (a b : Γ(X,U)) :
    bivectorSectionBracket f U (r • π) a b = r * bivectorSectionBracket f U π a b :=
  (bivectorSectionBracketLinear f U a b).map_smul r π

theorem bivectorSectionBracket_sum {I : Type*} (t : Finset I) (U : X.Opens)
    (π : I → Γ(bivectorSheaf f,U)) (a b : Γ(X,U)) :
    bivectorSectionBracket f U (t.sum π) a b =
      t.sum (fun i => bivectorSectionBracket f U (π i) a b) :=
  map_sum (bivectorSectionBracketLinear f U a b) π t

theorem bivectorSectionBracket_fintype_sum {I : Type*} [Fintype I] (U : X.Opens)
    (π : I → Γ(bivectorSheaf f,U)) (a b : Γ(X,U)) :
    bivectorSectionBracket f U (∑ i, π i) a b =
      ∑ i, bivectorSectionBracket f U (π i) a b :=
  bivectorSectionBracket_sum f Finset.univ U π a b

/-- Global bivector evaluation is additive on every actual open. -/
theorem algebraicBivectorBracket_add (U : X.Opens) (π τ : AlgebraicBivector f)
    (a b : Γ(X,U)) :
    (algebraicBivectorBracket f (π + τ)).bracket U a b =
      (algebraicBivectorBracket f π).bracket U a b +
        (algebraicBivectorBracket f τ).bracket U a b := by
  simp only [algebraicBivectorBracket_eq_sectionBracket, map_add]
  exact bivectorSectionBracket_add f U _ _ a b

@[simp] theorem algebraicBivectorBracket_zero (U : X.Opens) (a b : Γ(X,U)) :
    (algebraicBivectorBracket f 0).bracket U a b = 0 := by
  simp only [algebraicBivectorBracket_eq_sectionBracket, map_zero, bivectorSectionBracket_zero]

theorem algebraicBivectorBracket_sub (U : X.Opens) (π τ : AlgebraicBivector f)
    (a b : Γ(X,U)) :
    (algebraicBivectorBracket f (π - τ)).bracket U a b =
      (algebraicBivectorBracket f π).bracket U a b -
        (algebraicBivectorBracket f τ).bracket U a b := by
  simp only [algebraicBivectorBracket_eq_sectionBracket, map_sub]
  exact bivectorSectionBracket_sub f U _ _ a b

/-- Multiplying a global bivector multiplies its bracket by the actual
restriction of that global function to the evaluation open. -/
theorem algebraicBivectorBracket_smul (U : X.Opens) (r : Γ(X,⊤))
    (π : AlgebraicBivector f) (a b : Γ(X,U)) :
    (algebraicBivectorBracket f (r • π)).bracket U a b =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r *
        (algebraicBivectorBracket f π).bracket U a b := by
  simp only [algebraicBivectorBracket_eq_sectionBracket]
  have hm := (bivectorSheaf f).val.map_smul (homOfLE (le_top : U ≤ ⊤)).op r π
  change (show Γ(bivectorSheaf f,U) from
      (bivectorSheaf f).val.map (homOfLE (le_top : U ≤ ⊤)).op (r • π)) =
    (show Γ(X,U) from X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r) •
      (show Γ(bivectorSheaf f,U) from
        (bivectorSheaf f).val.map (homOfLE (le_top : U ≤ ⊤)).op π) at hm
  exact (congrArg (fun z : Γ(bivectorSheaf f,U) => bivectorSectionBracket f U z a b) hm).trans
    (bivectorSectionBracket_smul f U _ _ a b)

theorem algebraicBivectorBracket_sum {I : Type*} (t : Finset I) (U : X.Opens)
    (π : I → AlgebraicBivector f) (a b : Γ(X,U)) :
    (algebraicBivectorBracket f (t.sum π)).bracket U a b =
      t.sum (fun i => (algebraicBivectorBracket f (π i)).bracket U a b) := by
  simp only [algebraicBivectorBracket_eq_sectionBracket, map_sum]
  exact bivectorSectionBracket_sum f t U
    (fun i => (bivectorSheaf f).val.map (homOfLE (le_top : U ≤ ⊤)).op (π i)) a b

theorem algebraicBivectorBracket_fintype_sum {I : Type*} [Fintype I] (U : X.Opens)
    (π : I → AlgebraicBivector f) (a b : Γ(X,U)) :
    (algebraicBivectorBracket f (∑ i, π i)).bracket U a b =
      ∑ i, (algebraicBivectorBracket f (π i)).bracket U a b :=
  algebraicBivectorBracket_sum f Finset.univ U π a b

end NcCubic.Geometry

namespace NcCubic.Geometry.ProjectiveBivectorLinearity
attribute [local instance] MvPolynomial.gradedAlgebra
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveSpace.Cohomology
universe u

/-- Coefficient-ring scalar multiplication on actual global projective bivectors
is sent to the restriction of the actual coefficient scalar on every open. -/
theorem coefficient_smul (R : Type u) [CommRing R] (n : ℕ) {S : Scheme.{u}}
    (f : _root_.AlgebraicGeometry.Proj (polyGrading R n) ⟶ S) (U : (_root_.AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (r : R) (π : (twistCoefficientSections R n).obj (bivectorSheaf f))
    (a b : Γ(_root_.AlgebraicGeometry.Proj (polyGrading R n),U)) :
    (algebraicBivectorBracket f (r • π)).bracket U a b =
      (_root_.AlgebraicGeometry.Proj (polyGrading R n)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
        (coeffScalar R n r) * (algebraicBivectorBracket f π).bracket U a b :=
  algebraicBivectorBracket_smul f U (coeffScalar R n r) π a b

end NcCubic.Geometry.ProjectiveBivectorLinearity
