module
public import NcCubic.Geometry.BivectorSheafDesc
public import NcCubic.Geometry.TangentRelative
@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
namespace NcCubic.Geometry
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

theorem contractionHamiltonian_add (U : X.Opens) (c : Γ(tangentContractionSheaf f,U))
    (a b : Γ(X,U)) : contractionHamiltonian f U c (a+b) =
    contractionHamiltonian f U c a + contractionHamiltonian f U c b := by
  exact (congrArg (contractionEvaluation f U c)
    ((Scheme.Hom.universalRelativeDerivation f).d.map_add a b)).trans
      ((contractionEvaluation f U c).map_add _ _)

theorem contractionHamiltonian_mul (U : X.Opens) (c : Γ(tangentContractionSheaf f,U))
    (a b : Γ(X,U)) : contractionHamiltonian f U c (a*b) =
    a • contractionHamiltonian f U c b + b • contractionHamiltonian f U c a := by
  exact (congrArg (contractionEvaluation f U c)
    ((Scheme.Hom.universalRelativeDerivation f).d_mul a b)).trans
      (((contractionEvaluation f U c).map_add _ _).trans
        (congrArg₂ (·+·) ((contractionEvaluation f U c).map_smul a _)
          ((contractionEvaluation f U c).map_smul b _)))

theorem contractionSectionBracket_add_left (U : X.Opens)
    (c : Γ(tangentContractionSheaf f,U)) (a b d : Γ(X,U)) :
    contractionSectionBracket f U c (a+b) d =
      contractionSectionBracket f U c a d + contractionSectionBracket f U c b d := by
  change tangentEvaluation f U (contractionHamiltonian f U c (a+b)) _ = _
  rw [contractionHamiltonian_add,tangentEvaluation_add]
  rfl

theorem contractionSectionBracket_add_right (U : X.Opens)
    (c : Γ(tangentContractionSheaf f,U)) (a b d : Γ(X,U)) :
    contractionSectionBracket f U c a (b+d) =
      contractionSectionBracket f U c a b + contractionSectionBracket f U c a d :=
  (tangentSectionDerivation f U (contractionHamiltonian f U c a)).map_add b d

theorem contractionSectionBracket_mul_left (U : X.Opens)
    (c : Γ(tangentContractionSheaf f,U)) (a b d : Γ(X,U)) :
    contractionSectionBracket f U c (a*b) d =
      a*contractionSectionBracket f U c b d + b*contractionSectionBracket f U c a d := by
  change tangentEvaluation f U (contractionHamiltonian f U c (a*b)) _ = _
  rw [contractionHamiltonian_mul,tangentEvaluation_add,tangentEvaluation_smul,tangentEvaluation_smul]
  rfl

theorem contractionSectionBracket_mul_right (U : X.Opens)
    (c : Γ(tangentContractionSheaf f,U)) (a b d : Γ(X,U)) :
    contractionSectionBracket f U c a (b*d) =
      b*contractionSectionBracket f U c a d + d*contractionSectionBracket f U c a b := by
  exact (tangentSectionDerivation f U (contractionHamiltonian f U c a)).leibniz b d

theorem contractionSectionBracket_base_right (W : S.Opens) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ W) (c : Γ(tangentContractionSheaf f,U))
    (a : Γ(X,U)) (b : Γ(S,W)) :
    contractionSectionBracket f U c a ((f.appLE W U h).hom b) = 0 :=
  tangentSectionDerivation_base_appLE f W U h _ b

theorem contractionSectionBracket_base_left (W : S.Opens) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ W) (c : Γ(tangentContractionSheaf f,U))
    (a : Γ(S,W)) (b : Γ(X,U)) :
    contractionSectionBracket f U c ((f.appLE W U h).hom a) b = 0 := by
  have hd := (Scheme.Hom.universalRelativeDerivation f).d_map
    (homOfLE h).op ((f.app W).hom a)
  rw [Scheme.Hom.universalRelativeDerivation_d_app_eq_zero,map_zero] at hd
  change tangentEvaluation f U
    (contractionEvaluation f U c ((Scheme.Hom.universalRelativeDerivation f).d ((f.appLE W U h).hom a))) _ = 0
  have hd' : (Scheme.Hom.universalRelativeDerivation f).d ((f.appLE W U h).hom a) = 0 := hd
  have hH : contractionEvaluation f U c
      ((Scheme.Hom.universalRelativeDerivation f).d ((f.appLE W U h).hom a)) = 0 :=
    (congrArg (contractionEvaluation f U c) hd').trans (map_zero _)
  exact (congrArg (fun t => tangentEvaluation f U t ((Scheme.Hom.universalRelativeDerivation f).d b)) hH).trans
    (LinearMap.congr_fun ((tangentEvaluationLinear f U).map_zero) _)

variable (c : Γ(tangentContractionSheaf f,⊤))
theorem contractionGlobalBracket_add_left (U : X.Opens) (a b d : Γ(X,U)) :
    (contractionGlobalBracket f c).bracket U (a+b) d =
      (contractionGlobalBracket f c).bracket U a d + (contractionGlobalBracket f c).bracket U b d :=
  contractionSectionBracket_add_left f U _ a b d

theorem contractionGlobalBracket_add_right (U : X.Opens) (a b d : Γ(X,U)) :
    (contractionGlobalBracket f c).bracket U a (b+d) =
      (contractionGlobalBracket f c).bracket U a b + (contractionGlobalBracket f c).bracket U a d :=
  contractionSectionBracket_add_right f U _ a b d

theorem contractionGlobalBracket_mul_left (U : X.Opens) (a b d : Γ(X,U)) :
    (contractionGlobalBracket f c).bracket U (a*b) d =
      a*(contractionGlobalBracket f c).bracket U b d + b*(contractionGlobalBracket f c).bracket U a d :=
  contractionSectionBracket_mul_left f U _ a b d

theorem contractionGlobalBracket_mul_right (U : X.Opens) (a b d : Γ(X,U)) :
    (contractionGlobalBracket f c).bracket U a (b*d) =
      b*(contractionGlobalBracket f c).bracket U a d + d*(contractionGlobalBracket f c).bracket U a b :=
  contractionSectionBracket_mul_right f U _ a b d

section Base
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R)) (k : Γ(tangentContractionSheaf g,⊤))
theorem contractionGlobalBracket_coefficient_right (U : Y.Opens) (a : Γ(Y,U)) (r : R) :
    (contractionGlobalBracket g k).bracket U a (AffineSmoothness.coefficientMap g U r) = 0 :=
  contractionSectionBracket_base_right g ⊤ U le_top _ a ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)

theorem contractionGlobalBracket_coefficient_left (U : Y.Opens) (a : Γ(Y,U)) (r : R) :
    (contractionGlobalBracket g k).bracket U (AffineSmoothness.coefficientMap g U r) a = 0 :=
  contractionSectionBracket_base_left g ⊤ U le_top _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) a

theorem contractionGlobalBracket_coefficient_mul_left (U : Y.Opens) (a b : Γ(Y,U)) (r : R) :
    (contractionGlobalBracket g k).bracket U (AffineSmoothness.coefficientMap g U r * a) b =
      AffineSmoothness.coefficientMap g U r * (contractionGlobalBracket g k).bracket U a b := by
  rw [contractionGlobalBracket_mul_left,contractionGlobalBracket_coefficient_left,mul_zero,add_zero]

theorem contractionGlobalBracket_coefficient_mul_right (U : Y.Opens) (a b : Γ(Y,U)) (r : R) :
    (contractionGlobalBracket g k).bracket U a (AffineSmoothness.coefficientMap g U r * b) =
      AffineSmoothness.coefficientMap g U r * (contractionGlobalBracket g k).bracket U a b := by
  rw [contractionGlobalBracket_mul_right,contractionGlobalBracket_coefficient_right,mul_zero,add_zero]
end Base

theorem algebraicBivectorBracket_add_left (π : AlgebraicBivector f)
    (U : X.Opens) (a b d : Γ(X,U)) :
    (algebraicBivectorBracket f π).bracket U (a+b) d =
      (algebraicBivectorBracket f π).bracket U a d + (algebraicBivectorBracket f π).bracket U b d :=
  contractionGlobalBracket_add_left f _ U a b d

theorem algebraicBivectorBracket_add_right (π : AlgebraicBivector f)
    (U : X.Opens) (a b d : Γ(X,U)) :
    (algebraicBivectorBracket f π).bracket U a (b+d) =
      (algebraicBivectorBracket f π).bracket U a b + (algebraicBivectorBracket f π).bracket U a d :=
  contractionGlobalBracket_add_right f _ U a b d

theorem algebraicBivectorBracket_mul_left (π : AlgebraicBivector f)
    (U : X.Opens) (a b d : Γ(X,U)) :
    (algebraicBivectorBracket f π).bracket U (a*b) d =
      a*(algebraicBivectorBracket f π).bracket U b d + b*(algebraicBivectorBracket f π).bracket U a d :=
  contractionGlobalBracket_mul_left f _ U a b d

theorem algebraicBivectorBracket_mul_right (π : AlgebraicBivector f)
    (U : X.Opens) (a b d : Γ(X,U)) :
    (algebraicBivectorBracket f π).bracket U a (b*d) =
      b*(algebraicBivectorBracket f π).bracket U a d + d*(algebraicBivectorBracket f π).bracket U a b :=
  contractionGlobalBracket_mul_right f _ U a b d

section BivectorBase
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of R))
theorem algebraicBivectorBracket_coefficient_right (π : AlgebraicBivector g)
    (U : Y.Opens) (a : Γ(Y,U)) (r : R) :
    (algebraicBivectorBracket g π).bracket U a (AffineSmoothness.coefficientMap g U r) = 0 :=
  contractionGlobalBracket_coefficient_right g _ U a r

theorem algebraicBivectorBracket_coefficient_left (π : AlgebraicBivector g)
    (U : Y.Opens) (a : Γ(Y,U)) (r : R) :
    (algebraicBivectorBracket g π).bracket U (AffineSmoothness.coefficientMap g U r) a = 0 :=
  contractionGlobalBracket_coefficient_left g _ U a r

theorem algebraicBivectorBracket_coefficient_mul_left (π : AlgebraicBivector g)
    (U : Y.Opens) (a b : Γ(Y,U)) (r : R) :
    (algebraicBivectorBracket g π).bracket U (AffineSmoothness.coefficientMap g U r * a) b =
      AffineSmoothness.coefficientMap g U r * (algebraicBivectorBracket g π).bracket U a b :=
  contractionGlobalBracket_coefficient_mul_left g _ U a b r

theorem algebraicBivectorBracket_coefficient_mul_right (π : AlgebraicBivector g)
    (U : Y.Opens) (a b : Γ(Y,U)) (r : R) :
    (algebraicBivectorBracket g π).bracket U a (AffineSmoothness.coefficientMap g U r * b) =
      AffineSmoothness.coefficientMap g U r * (algebraicBivectorBracket g π).bracket U a b :=
  contractionGlobalBracket_coefficient_mul_right g _ U a b r
end BivectorBase
end NcCubic.Geometry
