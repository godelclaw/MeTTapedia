import Mettapedia.Computability.PNP.ClockedKpolyBridgeEquivalence
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible
import Mettapedia.Computability.PNP.ClockedKpolyGapAssessment

/-!
# PNP `Kpoly` coverage anchors: finite-cover and clocked interfaces

Generic equivalences between exact-visible compression, clocked realization, finite predictor-image covers, and clocked finite-learning payloads.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor for the `Kpoly` gap: at the current abstraction
level, a clocked exact-visible realization family is exactly an exact visible
compression target.  The remaining `Kpoly` burden is therefore a real
small-class theorem for the actual switched family, not clock bookkeeping. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_exactVisibleCompressionTarget
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  exists_clockedExactVisibleRealization_iff_exactVisibleCompressionTarget
    (G := G) (s := s) (clock := clock)

/-- Route-coverage anchor: the exact visible / clocked `Kpoly` target is exactly
a finite predictor-image cover of size at most `2^s`. -/
theorem kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorCover
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) :=
  exactVisibleCompressionTarget_iff_finitePredictorCover

/-- Route-coverage anchor: the clocked exact-visible realization interface has
the same finite predictor-image content. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_finitePredictorCover
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) :=
  exists_clockedExactVisibleRealization_iff_finitePredictorCover

/-- Route-coverage anchor: adding the accumulated finite-learning consequences
to the clocked bridge still has exactly the same finite predictor-image
content. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) :=
  clockedKpolyFiniteLearningPayload_iff_finitePredictorCover

/-- Route-coverage anchor: the accumulated finite-learning payload is exactly
the existing exact visible compression target. -/
theorem kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_exactVisibleCompressionTarget
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s :=
  clockedKpolyFiniteLearningPayload_iff_exactVisibleCompressionTarget


end Mettapedia.Computability.PNP
