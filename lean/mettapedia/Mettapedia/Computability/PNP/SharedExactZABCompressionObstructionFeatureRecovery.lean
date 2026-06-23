import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionFeatureTargets
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABRecoveryInterfaceSparseThreshold

/-!
# P vs NP crux: shared exact ZAB feature recovery obstruction

This module lifts the shared exact `(zfeat(z), a, b)` feature target
surface-cardinality obstructions through the affine-feature and
sparse-threshold recovery interfaces on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n p r k : ℕ} {Index : Type*}

/-- The shared-basis exact `(zfeat(z), a, b)` affine-feature recovery interface
inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABAffineFeatureRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the shared-basis exact `(zfeat(z), a, b)` affine-feature recovery
interface cannot be surjective once its exponential feature budget sits below
the full exact-surface threshold. -/
theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- In particular, the shared-basis exact `(zfeat(z), a, b)` affine-feature
recovery interface cannot be surjective when its shared affine width is
strictly smaller than the full exact visible width. -/
theorem SharedExactZABAffineFeatureRecoveryData.not_surjective_predict_of_lt_visibleWidth
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_lt_visibleWidth hfeat

/-- The shared-basis exact `(zfeat(z), a, b)` sparse-threshold recovery
interface inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABSparseThresholdRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the shared-basis exact `(zfeat(z), a, b)` sparse-threshold recovery
interface cannot be surjective once its linear threshold budget sits below the
full exact-surface threshold. -/
theorem SharedExactZABSparseThresholdRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 * p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

end

end Mettapedia.Computability.PNP
