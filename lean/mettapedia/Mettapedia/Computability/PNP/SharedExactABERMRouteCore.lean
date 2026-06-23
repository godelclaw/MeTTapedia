import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.SharedABDecisionListRecoveryInterface

/-!
# Shared exact `(a,b)` decision-list ERM route core

This module contains the ERM family and proves reduced `(a,b)` invariance and
shared decision-list realizability.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- The indexed exact-surface family obtained by running ERM inside the shared
raw exact `(a, b)` decision-list class. -/
noncomputable def sharedExactABAffineDecisionListERMFamily
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactABAffineDecisionListBitFamily Z features).indexedEmpiricalRiskFamily samples

theorem sharedExactABAffineDecisionListERMFamily_invariant
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ABVisibleInvariant
      (Z := Z) (k := k)
      (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples) := by
  intro i u v huv
  let code : SharedAffineDecisionListCode r :=
    (sharedAffineDecisionListCodeEquivBitCode r).symm
      ((sharedExactABAffineDecisionListBitFamily Z features).empiricalRiskCode (samples i))
  calc
    (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i u
      = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code u := by
          simp [sharedExactABAffineDecisionListERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABAffineDecisionListBitFamily,
            sharedAffineDecisionListCodeEquivBitCode]
    _ = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code v := by
          cases u
          cases v
          cases huv
          rfl
    _ = (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i v := by
          simp [sharedExactABAffineDecisionListERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABAffineDecisionListBitFamily,
            sharedAffineDecisionListCodeEquivBitCode]

theorem sharedExactABAffineDecisionListERMFamily_realized
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    RealizedBySharedABAffineDecisionListFamily
      (r := r) (k := k) features
      (liftToABVisibleFamily
        (Z := Z) (k := k)
        (sharedExactABAffineDecisionListERMFamily
          (Z := Z) (r := r) (k := k) features samples)) := by
  intro i
  let code : SharedAffineDecisionListCode r :=
    (sharedAffineDecisionListCodeEquivBitCode r).symm
      ((sharedExactABAffineDecisionListBitFamily Z features).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext x
  change
    (sharedExactABAffineDecisionListERMFamily
      (Z := Z) (r := r) (k := k) features samples).predict i
      (abVisibleSection (Z := Z) (k := k) x) =
    sharedABAffineDecisionListPredict (r := r) (k := k) features code x
  calc
    (sharedExactABAffineDecisionListERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i
        (abVisibleSection (Z := Z) (k := k) x)
      = sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code
          (abVisibleSection (Z := Z) (k := k) x) := by
          simp [sharedExactABAffineDecisionListERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABAffineDecisionListBitFamily,
            sharedAffineDecisionListCodeEquivBitCode]
    _ = sharedABAffineDecisionListPredict (r := r) (k := k) features code
          (abVisibleData (abVisibleSection (Z := Z) (k := k) x)) := by
          simpa using congrFun
            (sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code)
            (abVisibleSection (Z := Z) (k := k) x)
    _ = sharedABAffineDecisionListPredict (r := r) (k := k) features code x := by
          cases x
          rfl

end

end Mettapedia.Computability.PNP
