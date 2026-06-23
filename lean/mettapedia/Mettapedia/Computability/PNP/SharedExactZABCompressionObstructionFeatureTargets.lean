import Mettapedia.Computability.PNP.BitVecZABCompressionObstruction
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceData
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceAffineFeature
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceSparseThreshold
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionList
import Mettapedia.Computability.PNP.SharedExactZABTargetInterfaceDecisionListRecovery

/-!
# P vs NP crux: shared exact ZAB feature target obstruction

This module specializes exact visible surface-cardinality lower bounds to the
shared-basis exact `(zfeat(z), a, b)` affine-feature and sparse-threshold target
interfaces on `BitVec n`.
-/

namespace Mettapedia.Computability.PNP
section

variable {n p r k : ℕ} {Index : Type*}

/-- A shared-basis exact `(zfeat(z), a, b)` affine-feature target on `BitVec n`
still has to pay the full exact visible surface cardinality `2^(n + 2k)` if it
were surjective. -/
theorem SharedExactZABAffineFeatureTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 ^ p := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := 2 ^ p) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared-basis exact `(zfeat(z), a, b)` affine-feature target
cannot be surjective once its exponential feature budget sits below the full
exact-surface threshold. -/
theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hbudget : 2 ^ p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

/-- In particular, a shared-basis exact `(zfeat(z), a, b)` affine-feature
target cannot be surjective whenever its shared affine width is strictly
smaller than the full exact visible width. -/
theorem SharedExactZABAffineFeatureTargetData.not_surjective_predict_of_lt_visibleWidth
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABAffineFeatureTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hfeat : p < n + 2 * k) :
    ¬ Function.Surjective G.predict := by
  exact
    h.not_surjective_predict_of_budget_lt
      (Nat.pow_lt_pow_right Nat.one_lt_two hfeat)

/-- A shared-basis exact `(zfeat(z), a, b)` sparse-threshold target on
`BitVec n` still has to pay the full exact visible surface cardinality
`2^(n + 2k)` if it were surjective. -/
theorem SharedExactZABSparseThresholdTargetData.bitVecSurfaceCard_le_of_surjective_predict
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hsurj : Function.Surjective G.predict) :
    2 ^ (n + 2 * k) ≤ 2 * p := by
  exact
    exactVisibleCompressionTarget_bitVecSurfaceCard_le_of_surjective_predict
      (r := n) (k := k) (s := 2 * p) (Index := Index)
      hsurj h.compressionTarget

/-- Hence any shared-basis exact `(zfeat(z), a, b)` sparse-threshold target
cannot be surjective once its linear threshold budget sits below the full
exact-surface threshold. -/
theorem SharedExactZABSparseThresholdTargetData.not_surjective_predict_of_budget_lt
    {zfeat : BitVec n → BitVec r}
    {features : Fin p → AffineColumnCode (r + (k + k))}
    {G : ExactVisibleSwitchedFamily (BitVec n) k Index}
    (h :
      SharedExactZABSparseThresholdTargetData
        (Z := BitVec n) (p := p) (r := r) (k := k) (Index := Index)
        zfeat features G)
    (hbudget : 2 * p < 2 ^ (n + 2 * k)) :
    ¬ Function.Surjective G.predict := by
  intro hsurj
  exact Nat.not_le_of_lt hbudget <|
    h.bitVecSurfaceCard_le_of_surjective_predict hsurj

end

end Mettapedia.Computability.PNP
