import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.ExactZABERMInterface

/-!
# Exact ZAB compression obstruction: affine-feature layers

This module contains the non-shared exact affine-feature target, recovery,
ERM-family, and ERM-recovery surface bounds on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n p r k : ℕ} {Index : Type*}

theorem ExactZABAffineFeatureTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := p * ((r + (k + k)) + 1) + 2 ^ p) (Index := Index)
      hsurj h.compressionTarget

theorem ExactZABAffineFeatureTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      ExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) zfeat G)
    (hbudget : p * ((r + (k + k)) + 1) + 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineFeatureRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineFeatureRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : p * ((r + (k + k)) + 1) + 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

theorem exactZABAffineFeatureERMFamily_bitVecSurfaceCard_le_of_surjective_predict
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hsurj :
      Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat samples).predict) :
    2 ^ (n + 2 * k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  let hdata :=
    exactZABAffineFeatureERMTargetData
      (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) zfeat samples
  exact hdata.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem exactZABAffineFeatureERMFamily_not_surjective_of_budget_lt
    (zfeat : BitVec n → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface (BitVec n) k) Bool)
    (hbudget : p * ((r + (k + k)) + 1) + 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective
        (exactZABAffineFeatureERMFamily
          (Z := BitVec n) (p := p) (r := r) (k := k) zfeat samples).predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    exactZABAffineFeatureERMFamily_bitVecSurfaceCard_le_of_surjective_predict
      (n := n) (p := p) (r := r) (k := k) (Index := Index) zfeat samples hsurj

theorem ExactZABAffineFeatureERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ p * ((r + (k + k)) + 1) + 2 ^ p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

theorem ExactZABAffineFeatureERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      ExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : p * ((r + (k + k)) + 1) + 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

end

end Mettapedia.Computability.PNP
