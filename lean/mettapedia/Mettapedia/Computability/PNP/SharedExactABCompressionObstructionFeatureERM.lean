import Mettapedia.Computability.PNP.SharedExactABCompressionObstructionFeatureRecovery
import Mettapedia.Computability.PNP.SharedExactABFeatureERMInterfaceAffine
import Mettapedia.Computability.PNP.SharedExactABFeatureERMInterfaceSparseThreshold

/-!
# BitVec surface bounds for shared exact feature ERM wrappers

This module lifts the shared affine-feature and sparse-threshold obstructions to
the final exact ERM recovery interfaces.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n r k : ℕ} {Index : Type*}

/-- The final shared raw exact `(a, b)` affine-feature ERM interface inherits
the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactABAffineFeatureERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ r := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the final shared raw exact `(a, b)` affine-feature ERM interface
cannot be surjective once its exponential feature budget sits below the full
exact-surface threshold. -/
theorem SharedExactABAffineFeatureERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : 2 ^ r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- In particular, the final shared raw exact `(a, b)` affine-feature ERM
interface cannot be surjective when its shared affine width is strictly
smaller than the full exact visible width. -/
theorem SharedExactABAffineFeatureERMRecoveryData.not_surjective_predict_of_lt_visibleWidth
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABAffineFeatureERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hfeat : r < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_lt_visibleWidth hfeat

/-- The final shared raw exact `(a, b)` sparse-threshold ERM interface
inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactABSparseThresholdERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * r := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the final shared raw exact `(a, b)` sparse-threshold ERM interface
cannot be surjective once its linear threshold budget sits below the full
exact-surface threshold. -/
theorem SharedExactABSparseThresholdERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactABSparseThresholdERMRecoveryData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) μ G q)
    (hbudget : 2 * r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

end

end Mettapedia.Computability.PNP
