/- Lie identities used in the support construction of Lemma 3.2. -/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace NcCubic.SupportLie

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Compatibility before imposing a Lie algebra structure; the bracket is an
arbitrary bilinear map at this stage. -/
def Compatible (C : V →ₗ[K] V →ₗ[K] V) (H : LinearMap.BilinForm K V) : Prop :=
  ∀ a b c d, H (C a b) (C c d) + H (C b c) (C a d) + H (C c a) (C b d) = 0

/-- Alternation of a bilinear bracket implies its skew-symmetry, in every characteristic. -/
theorem skew_of_alternating (C : V →ₗ[K] V →ₗ[K] V)
    (hself : ∀ x, C x x = 0) (a b : V) : C a b = -C b a := by
  have h := hself (a + b)
  simp only [map_add, LinearMap.add_apply, hself, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left ((add_comm (C a b) (C b a)).trans h)

/-- Pairing a nested bracket against an invariant form moves the outside
bracket to the other entry, with the skew-symmetry sign. -/
theorem pair_nested (C : V →ₗ[K] V →ₗ[K] V) (B : LinearMap.BilinForm K V)
    (hself : ∀ x, C x x = 0)
    (hinv : ∀ a b c, B (C a b) c = B a (C b c)) (a b c d : V) :
    B (C a (C b c)) d = -B (C b c) (C a d) := by
  rw [skew_of_alternating C hself a (C b c), map_neg, LinearMap.neg_apply, hinv]

/-- Nondegeneracy, invariance and the four-variable compatibility identity
force the Leibniz/Jacobi identity, before a LieRing instance is constructed. -/
theorem leibniz_of_compatible (C : V →ₗ[K] V →ₗ[K] V)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hself : ∀ x, C x x = 0)
    (hinv : ∀ a b c, B (C a b) c = B a (C b c))
    (hK : Compatible C B) (a b c : V) :
    C a (C b c) = C (C a b) c + C b (C a c) := by
  apply sub_eq_zero.mp
  apply hB.1
  intro d
  simp only [map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply]
  rw [pair_nested C B hself hinv a b c d,
    pair_nested C B hself hinv b a c d, hinv (C a b) c d]
  have hk := hK a b c d
  rw [skew_of_alternating C hself c a, map_neg, LinearMap.neg_apply] at hk
  linear_combination -hk

/-- Build a Lie ring from the bilinear bracket and its compatible metric.
This is conditional linear algebra, not the existence of a support decomposition. -/
@[instance_reducible]
def lieRingOfCompatible (C : V →ₗ[K] V →ₗ[K] V)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hself : ∀ x, C x x = 0)
    (hinv : ∀ a b c, B (C a b) c = B a (C b c)) (hK : Compatible C B) : LieRing V where
  toAddCommGroup := inferInstance
  bracket := fun a b => C a b
  add_lie a b c := by simp
  lie_add a b c := by simp
  lie_self := hself
  leibniz_lie := leibniz_of_compatible C B hB hself hinv hK

/-- The Lie ring constructed above has the original scalar action. -/
@[instance_reducible]
def lieAlgebraOfCompatible (C : V →ₗ[K] V →ₗ[K] V)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hself : ∀ x, C x x = 0)
    (hinv : ∀ a b c, B (C a b) c = B a (C b c)) (hK : Compatible C B) :
    @LieAlgebra K V inferInstance (lieRingOfCompatible C B hB hself hinv hK) := by
  letI := lieRingOfCompatible C B hB hself hinv hK
  exact { toModule := inferInstance, lie_smul := fun t x y => (C x).map_smul t y }

/-- Perfectness and a nondegenerate invariant form force a zero center.
Perfectness here is stated as the span of all bracket values. -/
theorem eq_zero_of_central_of_bracket_span_eq_top
    (C : V →ₗ[K] V →ₗ[K] V) (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (hinv : ∀ a b c, B (C a b) c = B a (C b c))
    (hperfect : Submodule.span K (Set.range (fun p : V × V => C p.1 p.2)) = ⊤)
    (x : V) (hx : ∀ y, C x y = 0) : x = 0 := by
  have hs : Submodule.span K (Set.range (fun p : V × V => C p.1 p.2)) ≤
      LinearMap.ker (B x) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change B x (C a b) = 0
    rw [← hinv x a b, hx]
    simp
  apply hB.1 x
  intro y
  apply hs
  rw [hperfect]
  exact Submodule.mem_top

end NcCubic.SupportLie
