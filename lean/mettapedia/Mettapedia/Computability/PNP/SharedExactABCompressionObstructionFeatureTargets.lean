import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.SharedABRecoveryInterfaceSparseThreshold

/-!
# BitVec surface bounds for shared `(a,b)` feature targets

This module specializes exact visible compression obstruction bounds to the
shared affine-feature and sparse-threshold target interfaces.
-/

namespace Mettapedia.Computability.PNP

section

variable {n r k : ℕ} {Index : Type*}

/-- A shared raw exact `(a, b)` affine-feature target on `BitVec n` still has to
pay the full exact visible surface cardinality `2^(n + 2k)` if it were
surjective. -/
theorem SharedABAffineFeatureTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABAffineFeatureTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ r := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := 2 ^ r) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared raw exact `(a, b)` affine-feature target cannot be
surjective once its exponential feature budget sits below the full exact-surface
threshold. -/
theorem SharedABAffineFeatureTargetData.not_surjective_predict_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABAffineFeatureTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hbudget : 2 ^ r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- In particular, a shared raw exact `(a, b)` affine-feature target cannot be
surjective whenever its shared affine width is strictly smaller than the full
exact visible width. -/
theorem SharedABAffineFeatureTargetData.not_surjective_predict_of_lt_visibleWidth
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABAffineFeatureTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hfeat : r < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (Nat.pow_lt_pow_right Nat.one_lt_two hfeat)

/-- A shared raw exact `(a, b)` sparse-threshold target on `BitVec n` still has
to pay the full exact visible surface cardinality `2^(n + 2k)` if it were
surjective. -/
theorem SharedABSparseThresholdTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABSparseThresholdTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * r := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := 2 * r) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared raw exact `(a, b)` sparse-threshold target cannot be
surjective once its linear threshold budget sits below the full exact-surface
threshold. -/
theorem SharedABSparseThresholdTargetData.not_surjective_predict_of_budget_lt
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedABSparseThresholdTargetData
        (Z := BitVec n) (r := r) (k := k) (Index := Index) G)
    (hbudget : 2 * r < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

end

end Mettapedia.Computability.PNP
