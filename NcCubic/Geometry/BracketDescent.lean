module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
namespace NcCubic.Geometry.BracketDescent
variable {A B : Type*} [CommRing A] [CommRing B]

theorem congr_of_kernel (f : A →+* B) (op : A → A → A)
    (hadd : ∀ a b c, op a (b+c) = op a b + op a c)
    (hskew : ∀ a b,op a b = -op b a)
    (hker : ∀ a b,b ∈ RingHom.ker f → op a b ∈ RingHom.ker f)
    {a b a' b' : A} (ha : f a = f a') (hb : f b = f b') :
    f (op a b) = f (op a' b') := by
  have hz (a) : op a 0 = 0 := by have h := hadd a 0 0; simpa using h
  have hn (a b) : op a (-b) = -op a b := by
    have h := hadd a b (-b)
    rw [add_neg_cancel,hz] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hs (a b c) : op a (b-c) = op a b-op a c := by
    rw [sub_eq_add_neg,hadd,hn,sub_eq_add_neg]
  have hl (a b c) : op (a-b) c = op a c-op b c := by
    rw [hskew,hs,neg_sub,hskew c a,hskew c b]
    ring
  have hka : a-a' ∈ RingHom.ker f := by simp [RingHom.mem_ker,map_sub,ha]
  have hkb : b-b' ∈ RingHom.ker f := by simp [RingHom.mem_ker,map_sub,hb]
  have h1 : f (op (a-a') b) = 0 := by
    rw [hskew,map_neg,(RingHom.mem_ker.mp (hker b (a-a') hka)),neg_zero]
  have h2 := RingHom.mem_ker.mp (hker a' (b-b') hkb)
  rw [hl,map_sub] at h1
  rw [hs,map_sub] at h2
  exact (sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2)

def operation (f : A →+* B) (hf : Function.Surjective f) (op : A → A → A) (a b : B) : B :=
  f (op (hf a).choose (hf b).choose)

theorem operation_map (f : A →+* B) (hf : Function.Surjective f) (op : A → A → A)
    (hcongr : ∀ {a b a' b'},f a=f a' → f b=f b' → f (op a b)=f (op a' b'))
    (a b : A) : operation f hf op (f a) (f b) = f (op a b) := by
  exact hcongr ((hf (f a)).choose_spec) ((hf (f b)).choose_spec)

section Identities
variable (f : A →+* B) (hf : Function.Surjective f) (op : A → A → A)
  (hc : ∀ {a b a' b'}, f a = f a' → f b = f b' → f (op a b) = f (op a' b'))
include hc

theorem operation_add_right (hadd : ∀ a b c,op a (b+c)=op a b+op a c) (a b c : B) :
    operation f hf op a (b+c)=operation f hf op a b+operation f hf op a c := by
  obtain ⟨a,rfl⟩ := hf a
  obtain ⟨b,rfl⟩ := hf b
  obtain ⟨c,rfl⟩ := hf c
  rw [← map_add,operation_map f hf op hc,hadd,map_add,
    operation_map f hf op hc,operation_map f hf op hc]

theorem operation_skew (hs : ∀ a b,op a b = -op b a) (a b : B) :
    operation f hf op a b = -operation f hf op b a := by
  obtain ⟨a,rfl⟩ := hf a
  obtain ⟨b,rfl⟩ := hf b
  rw [operation_map f hf op hc,operation_map f hf op hc,hs,map_neg]

theorem operation_self (hs : ∀ a,op a a=0) (a : B) : operation f hf op a a=0 := by
  obtain ⟨a,rfl⟩ := hf a
  rw [operation_map f hf op hc,hs,map_zero]

theorem operation_leibniz (hm : ∀ a b c,op a (b*c)=b*op a c+c*op a b) (a b c : B) :
    operation f hf op a (b*c)=b*operation f hf op a c+c*operation f hf op a b := by
  obtain ⟨a,rfl⟩ := hf a
  obtain ⟨b,rfl⟩ := hf b
  obtain ⟨c,rfl⟩ := hf c
  rw [← map_mul,operation_map f hf op hc,hm,map_add,map_mul,map_mul,
    operation_map f hf op hc,operation_map f hf op hc]

theorem operation_jacobi (hJ : ∀ a b c,op a (op b c)+op b (op c a)+op c (op a b)=0)
    (a b c : B) : operation f hf op a (operation f hf op b c)+
    operation f hf op b (operation f hf op c a)+operation f hf op c (operation f hf op a b)=0 := by
  obtain ⟨a,rfl⟩ := hf a
  obtain ⟨b,rfl⟩ := hf b
  obtain ⟨c,rfl⟩ := hf c
  simp only [operation_map f hf op hc,← map_add,hJ,map_zero]
end Identities

/-- Descent commutes with a genuine commutative square of section-ring maps. -/
theorem operation_natural {C D : Type*} [CommRing C] [CommRing D]
    (f : A →+* B) (hf : Function.Surjective f) (op : A → A → A)
    (hc : ∀ {a b a' b'},f a=f a' → f b=f b' → f (op a b)=f (op a' b'))
    (g : C →+* D) (hg : Function.Surjective g) (op' : C → C → C)
    (hc' : ∀ {a b a' b'},g a=g a' → g b=g b' → g (op' a b)=g (op' a' b'))
    (r : A →+* C) (s : B →+* D) (hsquare : ∀ a,s (f a)=g (r a))
    (hnatural : ∀ a b,r (op a b)=op' (r a) (r b)) (a b : B) :
    s (operation f hf op a b)=operation g hg op' (s a) (s b) := by
  obtain ⟨a,rfl⟩ := hf a
  obtain ⟨b,rfl⟩ := hf b
  rw [operation_map f hf op hc,hsquare,hnatural,hsquare,hsquare,
    operation_map g hg op' hc']
end NcCubic.Geometry.BracketDescent
