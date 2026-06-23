import Mettapedia.Computability.PNP.ABDecisionListRoute
import Mettapedia.Computability.PNP.SharedExactABFeatureFamilies

/-!
# Shared `(a,b)` feature route predictors

This module contains the raw reduced-surface predictors and the definitional
equations relating them to their exact-surface counterparts through
`abVisibleData`.
-/

namespace Mettapedia.Computability.PNP

section

variable {Z : Type*} {r k : ℕ}

/-- Shared affine-feature predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABAffineFeaturePredict
    (features : Fin r → AffineColumnCode (k + k))
    (table : BitCode (2 ^ r))
    (x : ABVisibleSurface k) : Bool :=
  table ((Fintype.equivFinOfCardEq (by simp [BitVec] : Fintype.card (BitVec r) = 2 ^ r))
    (affineFeatureVector features (abVisibleBits (k := k) x)))

/-- Shared sparse-threshold predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABSparseThresholdAffinePredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedSparseThresholdCode r)
    (x : ABVisibleSurface k) : Bool :=
  decide (thresholdCodeValue (r := r) code.2 ≤
    maskedAffineFeatureCount (k := k + k) features code.1 (abVisibleBits (k := k) x))

/-- Shared decision-list predictor on the reduced raw surface `(a, b)`. -/
noncomputable def sharedABAffineDecisionListPredict
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedAffineDecisionListCode r)
    (x : ABVisibleSurface k) : Bool :=
  match firstActiveFeature? (affineFeatureVector features (abVisibleBits (k := k) x)) with
  | some j => code.1 j
  | none => code.2

theorem sharedExactABAffineFeaturePredict_eq_sharedABAffineFeaturePredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (table : BitCode (2 ^ r)) :
    sharedExactABAffineFeaturePredict (Z := Z) (k := k) features table =
      fun u => sharedABAffineFeaturePredict (k := k) features table (abVisibleData u) := by
  funext u
  cases u
  rfl

theorem sharedExactABSparseThresholdAffinePredict_eq_sharedABSparseThresholdAffinePredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedSparseThresholdCode r) :
    sharedExactABSparseThresholdAffinePredict (Z := Z) (k := k) features code =
      fun u => sharedABSparseThresholdAffinePredict (k := k) features code (abVisibleData u) := by
  funext u
  cases u
  rfl

theorem sharedExactABAffineDecisionListPredict_eq_sharedABAffineDecisionListPredict_comp_abVisibleData
    (features : Fin r → AffineColumnCode (k + k))
    (code : SharedAffineDecisionListCode r) :
    sharedExactABAffineDecisionListPredict (Z := Z) (k := k) features code =
      fun u => sharedABAffineDecisionListPredict (k := k) features code (abVisibleData u) := by
  funext u
  cases u
  rfl

end

end Mettapedia.Computability.PNP
