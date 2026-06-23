import Mettapedia.Computability.PNP.SharedExactZABCompressionObstructionFeatureRecovery
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABFeatureERMInterfaceSparseThreshold

/-!
# P vs NP crux: shared exact ZAB feature-ERM obstruction

This module lifts the shared exact `(zfeat(z), a, b)` feature recovery
surface-cardinality obstructions through the affine-feature and
sparse-threshold ERM recovery interfaces on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

section

variable {n p r k : ℕ} {Index : Type*}

/-- The final shared-basis exact `(zfeat(z), a, b)` affine-feature ERM
interface inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABAffineFeatureERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the final shared-basis exact `(zfeat(z), a, b)` affine-feature ERM
interface cannot be surjective once its exponential feature budget sits below
the full exact-surface threshold. -/
theorem SharedExactZABAffineFeatureERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

/-- In particular, the final shared-basis exact `(zfeat(z), a, b)`
affine-feature ERM interface cannot be surjective when its shared affine width
is strictly smaller than the full exact visible width. -/
theorem SharedExactZABAffineFeatureERMRecoveryData.not_surjective_predict_of_lt_visibleWidth
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABAffineFeatureERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_lt_visibleWidth hfeat

/-- The final shared-basis exact `(zfeat(z), a, b)` sparse-threshold ERM
interface inherits the same exact-surface lower bound on `BitVec n`. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.bitVecSurfaceCard_le_of_surjective_predict
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * p := by
  exact h.targetData.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- Hence the final shared-basis exact `(zfeat(z), a, b)` sparse-threshold ERM
interface cannot be surjective once its linear threshold budget sits below the
full exact-surface threshold. -/
theorem SharedExactZABSparseThresholdERMRecoveryData.not_surjective_predict_of_budget_lt
    {μ : PMF (ExactVisiblePostSwitchSurface (BitVec n) k)}
    {zfeat : BitVec n → BitVec r}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    {q : ℝ≥0∞}
    (h :
      SharedExactZABSparseThresholdERMRecoveryData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index) μ zfeat G q)
    (hbudget : 2 * p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  exact h.targetData.not_surjective_predict_of_budget_lt hbudget

end

end Mettapedia.Computability.PNP
