import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajoritySupport
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityCombinatorics
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityInterfaces
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityFallbackFamily
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityBitBounds
import Mettapedia.Computability.PNP.ActualSwitchedLocalBoundedSampleMajorityExactConsequences
import Mettapedia.Computability.PNP.ActualSwitchedLocalSharedExactZABSparseThresholdERMVisibleBudgetObstruction

/-!
# P vs NP route bridge: bounded-sample actual locality still faces the
  unconditional sparse-threshold visible-budget obstruction

`ActualSwitchedLocalSharedExactZABSparseThresholdERMVisibleBudgetObstruction`
showed that any surjective actual switched-local shared exact sparse-threshold
ERM packet must fit the exact visible surface inside the point-block bit budget
`2 * allAffinePointBlockFeatureCount (r + 2*k)`.  Separately,
`ActualSwitchedLocalBoundedSampleMajorityObstruction` characterizes when the
bounded-sample plug-in-majority actual-local family is surjective.

This file composes those facts at the bounded-sample manuscript-facing
endpoint.  Once the bounded sample bound is large enough for surjectivity, the
same visible-budget obstruction applies immediately, with no counting-gap
hypothesis and no recovery-side agreement estimate.

So on `BitVec n`, any such bounded-sample actual-local sparse-threshold packet
already forces

* `n ≤ 2*r + 2*k + 1`,

and is therefore impossible whenever `2*r + 2*k + 1 < n`.
-/

namespace Mettapedia.Computability.PNP

namespace ActualSwitchedLocalInterface

section Abstract

universe u v

variable {Z : Type v} [Fintype Z] {k r sampleBound : ℕ}
variable {zfeat : Z → BitVec r}

/-- At the bounded-sample plug-in-majority actual-local endpoint, nonempty
shared exact sparse-threshold ERM data plus the standard surjectivity-side
sample-bound hypothesis already forces the exact visible surface to fit inside
the point-block sparse-threshold bit budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_surfaceCard_le_of_nonempty_sharedExactZABSparseThresholdERMData
    (hdata :
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat))
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound) :
    Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤
      2 * allAffinePointBlockFeatureCount (r + (k + k)) := by
  rcases hdata with ⟨h⟩
  exact
    h.surfaceCard_le_of_surjective_predict
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hsample)

/-- Therefore the bounded-sample plug-in-majority actual-local endpoint cannot
carry shared exact sparse-threshold ERM data when the exact visible surface is
already larger than the point-block sparse-threshold bit budget. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_lt_surfaceCard
    (hsample : Fintype.card (ExactVisiblePostSwitchSurface Z k) ≤ sampleBound)
    (hs :
      2 * allAffinePointBlockFeatureCount (r + (k + k)) <
        Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
          zfeat) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_lt_surfaceCard
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface Z k sampleBound)
      zfeat
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        Z k sampleBound hsample)
      hs

end Abstract

section BitVec

universe u

variable {n k r sampleBound : ℕ}
variable {zfeat : BitVec n → BitVec r}

/-- On `BitVec n`, the bounded-sample plug-in-majority actual-local endpoint
inherits the same unconditional extractor-width lower bound once the sample
bound is large enough for surjectivity. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_nonempty_sharedExactZABSparseThresholdERMData
    (hdata :
      Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat))
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound) :
    n ≤ 2 * r + 2 * k + 1 := by
  rcases hdata with ⟨h⟩
  exact
    h.visibleWidth_le_two_mul_extractorWidth_add_two_mul_k_succ_of_surjective_predict
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        (BitVec n) k sampleBound hsample)

/-- Hence the bounded-sample plug-in-majority actual-local endpoint cannot
carry shared exact sparse-threshold ERM data below the unconditional
point-block visible-width threshold, even without the counting-gap packet. -/
theorem boundedSamplePluginMajorityActualSwitchedLocalInterface_not_nonempty_sharedExactZABSparseThresholdERMData_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
    (hsample :
      Fintype.card (ExactVisiblePostSwitchSurface (BitVec n) k) ≤ sampleBound)
    (hgap : 2 * r + 2 * k + 1 < n) :
    ¬ Nonempty
        (SharedExactZABSparseThresholdERMData
          (boundedSamplePluginMajorityActualSwitchedLocalInterface
            (BitVec n) k sampleBound)
          zfeat) := by
  exact
    not_nonempty_sharedExactZABSparseThresholdERMData_of_surjective_predict_of_two_mul_extractorWidth_add_two_mul_k_succ_lt_visibleWidth
      (T := boundedSamplePluginMajorityActualSwitchedLocalInterface
        (BitVec n) k sampleBound)
      zfeat
      (boundedSamplePluginMajorityActualSwitchedLocalInterface_surjective
        (BitVec n) k sampleBound hsample)
      hgap

end BitVec

end ActualSwitchedLocalInterface

end Mettapedia.Computability.PNP
