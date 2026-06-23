import Mettapedia.Computability.PNP.BitFamilyERM
import Mettapedia.Computability.PNP.SharedABRecoveryInterfaceSparseThreshold

/-!
# Shared exact `(a,b)` affine-feature ERM route core

This module contains the ERM families and proves their reduced `(a,b)`
invariance and shared-feature realizability.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ} {Index : Type*}

/-- ERM inside the shared raw exact `(a, b)` affine-feature class. -/
noncomputable def sharedExactABAffineFeatureERMFamily
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactABAffineFeatureBitFamily Z features).indexedEmpiricalRiskFamily samples

/-- ERM inside the shared raw exact `(a, b)` sparse-threshold class. -/
noncomputable def sharedExactABSparseThresholdAffineERMFamily
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ExactVisibleSwitchedFamily Z k Index :=
  (sharedExactABSparseThresholdAffineBitFamily Z features).indexedEmpiricalRiskFamily samples

theorem sharedExactABAffineFeatureERMFamily_invariant
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ABVisibleInvariant
      (Z := Z) (k := k)
      (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples) := by
  intro i u v huv
  let table : BitCode (2 ^ r) :=
    (sharedExactABAffineFeatureBitFamily Z features).empiricalRiskCode (samples i)
  calc
    (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i u
      = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table u := by
          simp [sharedExactABAffineFeatureERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            table,
            sharedExactABAffineFeatureBitFamily]
    _ = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table v := by
          cases u
          cases v
          cases huv
          rfl
    _ = (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i v := by
          simp [sharedExactABAffineFeatureERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            table,
            sharedExactABAffineFeatureBitFamily]

theorem sharedExactABSparseThresholdAffineERMFamily_invariant
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ABVisibleInvariant
      (Z := Z) (k := k)
      (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples) := by
  intro i u v huv
  let code : SharedSparseThresholdCode r :=
    (sharedSparseThresholdCodeEquivBitCode r).symm
      ((sharedExactABSparseThresholdAffineBitFamily Z features).empiricalRiskCode (samples i))
  calc
    (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i u
      = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code u := by
          simp [sharedExactABSparseThresholdAffineERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABSparseThresholdAffineBitFamily,
            sharedSparseThresholdCodeEquivBitCode]
    _ = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code v := by
          cases u
          cases v
          cases huv
          rfl
    _ = (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples).predict i v := by
          simp [sharedExactABSparseThresholdAffineERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABSparseThresholdAffineBitFamily,
            sharedSparseThresholdCodeEquivBitCode]

theorem sharedExactABAffineFeatureERMFamily_realized
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    RealizedBySharedABAffineFeatureFamily
      (r := r) (k := k) features
      (liftToABVisibleFamily
        (Z := Z) (k := k)
        (sharedExactABAffineFeatureERMFamily
          (Z := Z) (r := r) (k := k) features samples)) := by
  intro i
  let table : BitCode (2 ^ r) :=
    (sharedExactABAffineFeatureBitFamily Z features).empiricalRiskCode (samples i)
  refine ⟨table, ?_⟩
  funext x
  change
    (sharedExactABAffineFeatureERMFamily
      (Z := Z) (r := r) (k := k) features samples).predict i
      (abVisibleSection (Z := Z) (k := k) x) =
    sharedABAffineFeaturePredict (r := r) (k := k) features table x
  calc
    (sharedExactABAffineFeatureERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i
        (abVisibleSection (Z := Z) (k := k) x)
      = sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table
          (abVisibleSection (Z := Z) (k := k) x) := by
          simp [sharedExactABAffineFeatureERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            table,
            sharedExactABAffineFeatureBitFamily]
    _ = sharedABAffineFeaturePredict (r := r) (k := k) features table
          (abVisibleData (abVisibleSection (Z := Z) (k := k) x)) := by
          simpa using congrFun
            (sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features table)
            (abVisibleSection (Z := Z) (k := k) x)
    _ = sharedABAffineFeaturePredict (r := r) (k := k) features table x := by
          cases x
          rfl

theorem sharedExactABSparseThresholdAffineERMFamily_realized
    [Inhabited Z]
    (features : Fin r → AffineColumnCode (k + k))
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    RealizedBySharedABSparseThresholdAffineFamily
      (r := r) (k := k) features
      (liftToABVisibleFamily
        (Z := Z) (k := k)
        (sharedExactABSparseThresholdAffineERMFamily
          (Z := Z) (r := r) (k := k) features samples)) := by
  intro i
  let code : SharedSparseThresholdCode r :=
    (sharedSparseThresholdCodeEquivBitCode r).symm
      ((sharedExactABSparseThresholdAffineBitFamily Z features).empiricalRiskCode (samples i))
  refine ⟨code, ?_⟩
  funext x
  change
    (sharedExactABSparseThresholdAffineERMFamily
      (Z := Z) (r := r) (k := k) features samples).predict i
      (abVisibleSection (Z := Z) (k := k) x) =
    sharedABSparseThresholdAffinePredict (r := r) (k := k) features code x
  calc
    (sharedExactABSparseThresholdAffineERMFamily
        (Z := Z) (r := r) (k := k) features samples).predict i
        (abVisibleSection (Z := Z) (k := k) x)
      = sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code
          (abVisibleSection (Z := Z) (k := k) x) := by
          simp [sharedExactABSparseThresholdAffineERMFamily,
            BitEncodedClassifierFamily.indexedEmpiricalRiskFamily,
            BitEncodedClassifierFamily.empiricalRiskPredictor,
            code,
            sharedExactABSparseThresholdAffineBitFamily,
            sharedSparseThresholdCodeEquivBitCode]
    _ = sharedABSparseThresholdAffinePredict (r := r) (k := k) features code
          (abVisibleData (abVisibleSection (Z := Z) (k := k) x)) := by
          simpa using congrFun
            (sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
              (Z := Z) (r := r) (k := k) features code)
            (abVisibleSection (Z := Z) (k := k) x)
    _ = sharedABSparseThresholdAffinePredict (r := r) (k := k) features code x := by
          cases x
          rfl

end

end Mettapedia.Computability.PNP
