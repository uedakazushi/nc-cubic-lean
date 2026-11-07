/-
Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Project-local implementation; upstream dependencies retain their licenses.
-/
module
public import NcCubic.Geometry.LocalizedBracket
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.LinearCombination
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.HomogeneousBasic
open MvPolynomial
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {N : ℕ}

/-- A genuine degree-zero homogeneous fraction admits a representative
with positive denominator exponent and a homogeneous numerator. -/
theorem exists_positive_rep {h : CubicPolynomial N} {d : ℕ} (hh : h.IsHomogeneous d)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    ∃ (n : ℕ) (a : CubicPolynomial N), 0 < n ∧ a.IsHomogeneous (n*d) ∧
      (algebraMap (CubicPolynomial N) (Localization.Away h) h)^n * x.val =
        algebraMap _ (Localization.Away h) a := by
  have he := (HomogeneousLocalization.Away.eventually_smul_mem
    (𝒜 := homogeneousSubmodule (Fin N) ℂ) hh x).and (Filter.eventually_gt_atTop 0)
  obtain ⟨n,⟨a,ha,heq⟩,hn⟩ := he.exists
  refine ⟨n,a,hn,?_,?_⟩
  · change a.IsHomogeneous (n • d) at ha
    simpa only [nsmul_eq_mul,Nat.cast_id] using ha
  · simpa only [Algebra.smul_def,map_pow] using heq.symm

/-- The cleared numerator of a derivative of a homogeneous fraction. -/
def derivativeNumerator (h a : CubicPolynomial N) (n : ℕ) (i : Fin N) :=
  h*pderiv i a - C (n : ℂ)*a*pderiv i h

theorem derivativeNumerator_homogeneous {h a : CubicPolynomial N} {d n : ℕ}
    (hd : 0 < d) (hn : 0 < n) (hh : h.IsHomogeneous d) (ha : a.IsHomogeneous (n*d))
    (i : Fin N) : (derivativeNumerator h a n i).IsHomogeneous ((n+1)*d-1) := by
  have hnd := Nat.mul_pos hn hd
  unfold derivativeNumerator
  apply IsHomogeneous.sub
  · convert hh.mul (ha.pderiv (i:=i)) using 1
    simp only [Nat.add_mul,one_mul]
    omega
  · convert (ha.C_mul (n : ℂ)).mul (hh.pderiv (i:=i)) using 1
    simp only [Nat.add_mul,one_mul]
    omega

/-- Differentiating a denominator-cleared representative gives a homogeneous
numerator with one additional denominator power. -/
theorem derivative_cleared {h a : CubicPolynomial N} {n : ℕ} (hn : 0 < n)
    (x : Localization.Away h)
    (hx : (algebraMap (CubicPolynomial N) (Localization.Away h) h)^n*x = algebraMap _ _ a)
    (i : Fin N) :
    (algebraMap (CubicPolynomial N) (Localization.Away h) h)^(n+1) *
        LocalizedPoisson.localizedPderiv (Submonoid.powers h) (Localization.Away h) i x =
      algebraMap _ _ (derivativeNumerator h a n i) := by
  let t := algebraMap (CubicPolynomial N) (Localization.Away h) h
  let D := LocalizedPoisson.localizedPderiv (Submonoid.powers h) (Localization.Away h) i
  have ht : t * t^(n-1) = t^n := by
    rw [← pow_succ']
    congr 1
    omega
  have hd := congrArg D hx
  simp only [Derivation.leibniz,Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,
    D,LocalizedPoisson.localizedPderiv,Derivation.localization_algebraMap] at hd
  change t^n * D x + x * ((n : Localization.Away h) *
    (t^(n-1) * algebraMap _ _ (pderiv i h))) = algebraMap _ _ (pderiv i a) at hd
  change t^(n+1)*D x = _
  simp only [derivativeNumerator,map_sub,map_mul]
  have hh' : algebraMap (CubicPolynomial N) (Localization.Away h) (C (n : ℂ)) = (n : Localization.Away h) := by
    change (algebraMap ℂ (Localization.Away h)) (n : ℂ) = _
    simp
  rw [hh']
  rw [pow_succ']
  calc
    t*t^n*D x = t*algebraMap _ _ (pderiv i a) -
      (n : Localization.Away h)* (t*t^(n-1)) * x * algebraMap _ _ (pderiv i h) := by
        linear_combination t * hd
    _ = _ := by rw [ht]; rw [mul_assoc (n : Localization.Away h),hx]
/-- The polynomial numerator of the full bracket after clearing denominators. -/
def bracketNumerator (q : Fin N → Fin N → CubicPolynomial N)
    (h a b : CubicPolynomial N) (n m : ℕ) : CubicPolynomial N :=
  ∑ i, ∑ j, q i j * derivativeNumerator h a n i * derivativeNumerator h b m j

theorem bracketNumerator_homogeneous
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h a b : CubicPolynomial N} {d n m : ℕ} (hd : 0 < d) (hn : 0 < n) (hm : 0 < m)
    (hh : h.IsHomogeneous d) (ha : a.IsHomogeneous (n*d)) (hb : b.IsHomogeneous (m*d)) :
    (bracketNumerator q h a b n m).IsHomogeneous ((n+m+2)*d) := by
  have hnD := Nat.mul_pos (by omega : 0 < n+1) hd
  have hmD := Nat.mul_pos (by omega : 0 < m+1) hd
  unfold bracketNumerator
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  convert ((hq i j).mul (derivativeNumerator_homogeneous hd hn hh ha i)).mul
    (derivativeNumerator_homogeneous hd hm hh hb j) using 1
  simp only [Nat.add_mul,one_mul,two_mul] at *
  omega

theorem bracket_cleared
    (q : Fin N → Fin N → CubicPolynomial N)
    {h a b : CubicPolynomial N} {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (x y : Localization.Away h)
    (hx : (algebraMap (CubicPolynomial N) (Localization.Away h) h)^n*x = algebraMap _ _ a)
    (hy : (algebraMap (CubicPolynomial N) (Localization.Away h) h)^m*y = algebraMap _ _ b) :
    (algebraMap (CubicPolynomial N) (Localization.Away h) h)^(n+m+2) *
      LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q x y =
        algebraMap _ _ (bracketNumerator q h a b n m) := by
  rw [show n+m+2=(n+1)+(m+1) by omega,pow_add]
  simp only [LocalizedPoisson.bracket,bracketNumerator,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul,map_mul]
  calc
    _ = algebraMap _ _ (q i j) *
      ((algebraMap (CubicPolynomial N) (Localization.Away h) h)^(n+1) *
        LocalizedPoisson.localizedPderiv (Submonoid.powers h) (Localization.Away h) i x) *
      ((algebraMap (CubicPolynomial N) (Localization.Away h) h)^(m+1) *
        LocalizedPoisson.localizedPderiv (Submonoid.powers h) (Localization.Away h) j y) := by ring
    _ = _ := by rw [derivative_cleared hn x hx i,derivative_cleared hm y hy j]

/-- A homogeneous quadratic ambient bivector preserves the genuine degree-zero
ring on every positive homogeneous projective basic open. -/
theorem bracket_preserves_degreeZero
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    ∃ z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h,
      z.val = LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q x.val y.val := by
  classical
  obtain ⟨n,a,hn,ha,hx⟩ := exists_positive_rep hh x
  obtain ⟨m,b,hm,hb,hy⟩ := exists_positive_rep hh y
  let A := bracketNumerator q h a b n m
  have hA : A ∈ homogeneousSubmodule (Fin N) ℂ ((n+m+2) • d) := by
    change A.IsHomogeneous ((n+m+2) • d)
    simpa only [nsmul_eq_mul,Nat.cast_id] using
      (bracketNumerator_homogeneous q hq hd hn hm hh ha hb)
  refine ⟨HomogeneousLocalization.Away.mk (homogeneousSubmodule (Fin N) ℂ) hh (n+m+2) A hA,?_⟩
  change Localization.mk A (⟨h^(n+m+2), by exact ⟨n+m+2,rfl⟩⟩ : Submonoid.powers h) = _
  rw [Localization.mk_eq_mk']
  symm
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  simpa only [Subtype.coe_mk,map_pow,mul_comm] using bracket_cleared q hn hm x.val y.val hx hy
/-- The canonical bracket on every actual positive homogeneous basic-open ring. -/
def bracket (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :=
  (bracket_preserves_degreeZero q hq hd hh x y).choose

@[simp] theorem bracket_val
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    (bracket q hq hd hh x y).val =
      LocalizedPoisson.bracket (Submonoid.powers h) (Localization.Away h) q x.val y.val :=
  (bracket_preserves_degreeZero q hq hd hh x y).choose_spec

theorem bracket_self
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    (hskew : ∀ i j,q j i = -q i j)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    bracket q hq hd hh x x = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [bracket_val,HomogeneousLocalization.val_zero]
  exact LocalizedPoisson.bracket_self q hskew x.val

theorem bracket_skew
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    (hskew : ∀ i j,q j i = -q i j)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    bracket q hq hd hh x y = -bracket q hq hd hh y x := by
  apply HomogeneousLocalization.val_injective
  simp only [bracket_val,HomogeneousLocalization.val_neg]
  exact LocalizedPoisson.bracket_skew q hskew x.val y.val

theorem bracket_add_right
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    bracket q hq hd hh x (y+z) = bracket q hq hd hh x y + bracket q hq hd hh x z := by
  apply HomogeneousLocalization.val_injective
  simp only [bracket_val,HomogeneousLocalization.val_add,LocalizedPoisson.bracket_add_right]

theorem bracket_leibniz
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    bracket q hq hd hh x (y*z) = y*bracket q hq hd hh x z + z*bracket q hq hd hh x y := by
  apply HomogeneousLocalization.val_injective
  simp only [bracket_val,HomogeneousLocalization.val_add,HomogeneousLocalization.val_mul,
    LocalizedPoisson.bracket_mul_right]

theorem bracket_jacobi
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    (hskew : ∀ i j,q j i = -q i j) (hJac : SatisfiesJacobi (bracketFromCoefficients q))
    {h : CubicPolynomial N} {d : ℕ} (hd : 0 < d) (hh : h.IsHomogeneous d)
    (x y z : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) h) :
    bracket q hq hd hh x (bracket q hq hd hh y z) +
    bracket q hq hd hh y (bracket q hq hd hh z x) +
    bracket q hq hd hh z (bracket q hq hd hh x y) = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [bracket_val,HomogeneousLocalization.val_add,HomogeneousLocalization.val_zero]
  exact LocalizedPoisson.bracket_jacobi q hskew hJac x.val y.val z.val

/-- The ambient map of actual affine localizations associated to a refinement. -/
def ambientRestriction {f g x : CubicPolynomial N} (hx : x = f*g) :
    Localization.Away f →ₐ[CubicPolynomial N] Localization.Away x :=
  IsLocalization.Away.liftAlgHom (f := Algebra.ofId (CubicPolynomial N) (Localization.Away x))
    f (isUnit_of_dvd_unit (map_dvd _ ⟨g,hx⟩) (IsLocalization.Away.algebraMap_isUnit x))

/-- The actual homogeneous restriction between basic-open rings. -/
def restriction {f g x : CubicPolynomial N} {e : ℕ}
    (hg : g.IsHomogeneous e) (hx : x = f*g) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) f →+*
      HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) x :=
  HomogeneousLocalization.awayMap (homogeneousSubmodule (Fin N) ℂ) hg hx

theorem restriction_val {f g x : CubicPolynomial N} {e : ℕ}
    (hg : g.IsHomogeneous e) (hx : x = f*g)
    (a : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) f) :
    (restriction hg hx a).val = ambientRestriction hx a.val := by
  exact (HomogeneousLocalization.val_awayMap (homogeneousSubmodule (Fin N) ℂ)
    (show g ∈ homogeneousSubmodule (Fin N) ℂ e from hg) hx a).trans (by rfl)

/-- Compatibility with actual projective basic-open restrictions on all sections. -/
theorem bracket_restriction
    (q : Fin N → Fin N → CubicPolynomial N) (hq : ∀ i j,(q i j).IsHomogeneous 2)
    {f g x : CubicPolynomial N} {d e : ℕ}
    (hd : 0 < d) (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hx : x = f*g)
    (a b : HomogeneousLocalization.Away (homogeneousSubmodule (Fin N) ℂ) f) :
    restriction hg hx (bracket q hq hd hf a b) =
      bracket q hq (by omega : 0 < d+e) (hx ▸ hf.mul hg)
        (restriction hg hx a) (restriction hg hx b) := by
  apply HomogeneousLocalization.val_injective
  simp only [bracket_val,restriction_val]
  exact LocalizedPoisson.bracket_natural q (ambientRestriction hx) a.val b.val
end NcCubic.Geometry.HomogeneousBasic
