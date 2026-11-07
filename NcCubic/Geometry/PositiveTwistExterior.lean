/- Copyright (c) 2026 nc-cubic contributors. All rights reserved.
Adapted from StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso,
pinned Stacks revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7 (Apache 2.0).
The same Pascal decomposition is applied to the positive twist. -/
module
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.ExteriorPowerSumIso
set_option maxHeartbeats 1000000
@[expose] public noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace NcCubic.Geometry.ProjectiveCohomology
universe u
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistRank
attribute [local instance] hasFiniteBiproducts_toRingCat
variable (R : Type u) [CommRing R] (n : ℕ)
def positive_wedgeOneSingletonIso :
    wedge R n (twistSum R n (1) 1) 1 ≅ twistSum R n (((1 : ℕ) : ℤ)) 1 :=
  (_root_.SheafOfModules.algebras _ (twistSum R n (1) 1)).exteriorPowerOneIso ≪≫
    eqToIso (congrArg (fun c : ℤ => twistSum R n c 1)
      (by norm_num : (1 : ℤ) = ((1 : ℕ) : ℤ)))


def positive_wedgeHighSingletonIso (q : ℕ) :
    wedge R n (twistSum R n (1) 1) (q + 2) ≅
      twistSum R n (((q + 2 : ℕ) : ℤ)) (Nat.choose 1 (q + 2)) :=
  IsZero.iso
    ((isZero_exteriorPower_twistingSheaf R n (1) (by omega : 1 < q + 2)).of_iso
      (wedgeMapIso R n (F := twistSum R n (1) 1) (G := twistObj R n (1))
        (biproductUniqueIso _) (q + 2)))
    (isZero_biproductFin (twistObj R n (((q + 2 : ℕ) : ℤ)))
      (Nat.choose_eq_zero_of_lt (by omega)))


theorem positive_nonempty_wedgeTwistSingletonIso : ∀ q : ℕ,
    Nonempty (wedge R n (twistSum R n (1) 1) q ≅
      twistSum R n (((q : ℕ) : ℤ)) (Nat.choose 1 q)) := by
  intro q
  rcases q with _ | q
  · simpa using (show Nonempty (wedge R n (twistSum R n 1 1) 0 ≅ twistSum R n 0 1) from ⟨wedgeZeroIso R n _⟩)
  rcases q with _ | q
  · exact ⟨positive_wedgeOneSingletonIso R n⟩
  · exact ⟨positive_wedgeHighSingletonIso R n q⟩

/-! ### The induction on the number of summands -/


def positive_wedgeTwistSumSuccIso (N q : ℕ)
    (e1 : wedge R n (twistSum R n (1) (N + 1)) (q + 1) ≅
      twistSum R n (((q + 1 : ℕ) : ℤ)) ((N + 1).choose (q + 1)))
    (e0 : wedge R n (twistSum R n (1) (N + 1)) q ≅
      twistSum R n (((q : ℕ) : ℤ)) ((N + 1).choose q)) :
    wedge R n (twistSum R n (1) (N + 2)) (q + 1) ≅
      twistSum R n (((q + 1 : ℕ) : ℤ)) ((N + 2).choose (q + 1)) :=
  (exteriorPowerSplitIso (Y := _root_.AlgebraicGeometry.Proj (polyGrading R n))
        (twistFamily R n (1) (N + 2))
        (fun _ hk => isZero_exteriorPower_twistingSheaf R n (1) hk) q).symm ≪≫
    biprod.mapIso e1
      (tensorObjMapIso R n (twistObj R n (1)) e0 ≪≫
        tensorTwistSumIso R n (1) (((q : ℕ) : ℤ)) ((N + 1).choose q) ≪≫
        eqToIso (congrArg (fun c : ℤ => twistSum R n c ((N + 1).choose q))
          (by push_cast; ring : (1 : ℤ) + ((q : ℕ) : ℤ) = ((q + 1 : ℕ) : ℤ)))) ≪≫
    twistSumAddIso R n (((q + 1 : ℕ) : ℤ)) ((N + 1).choose (q + 1)) ((N + 1).choose q) ≪≫
    biprodFinCongr (twistObj R n (((q + 1 : ℕ) : ℤ))) (choose_succ_add_choose N q)


theorem positive_nonempty_wedgeTwistSumIso (N : ℕ) : ∀ q : ℕ,
    Nonempty (wedge R n (twistSum R n (1) (N + 1)) q ≅
      twistSum R n (((q : ℕ) : ℤ)) ((N + 1).choose q)) := by
  induction N with
  | zero => exact positive_nonempty_wedgeTwistSingletonIso R n
  | succ N ih =>
    intro q
    rcases q with _ | q
    · simpa using (show Nonempty (wedge R n (twistSum R n 1 (N + 1 + 1)) 0 ≅ twistSum R n 0 1) from ⟨wedgeZeroIso R n _⟩)
    · exact ⟨positive_wedgeTwistSumSuccIso R n N q (ih (q + 1)).some (ih q).some⟩


/-- The actual positive-twist exterior-sum comparison, obtained from the
proved Pascal decomposition. The ambient projective dimension is `n`. -/
def positiveTwistSumExteriorIso (N q : ℕ) :
    wedge R n (twistSum R n 1 (N + 1)) q ≅
      twistSum R n (q : ℤ) ((N + 1).choose q) :=
  (positive_nonempty_wedgeTwistSumIso R n N q).some

end NcCubic.Geometry.ProjectiveCohomology
