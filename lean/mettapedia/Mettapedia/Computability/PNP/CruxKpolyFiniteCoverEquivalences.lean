import Mettapedia.Computability.PNP.ExactVisibleImageBudgetFiniteCovers
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetLowerBounds
import Mettapedia.Computability.PNP.ExactVisibleImageBudgetExactVisible

/-!
# PNP `Kpoly` finite-cover equivalence anchors

This module collects the equivalences between exact-visible compression,
clocked realization, finite predictor-image covers, representative-index
covers, quotient-code presentations, and their monotonicity rules.
-/

namespace Mettapedia.Computability.PNP
universe u v w z

/-- Route-coverage anchor: exact visible compression is equivalently a finite
quotient-code presentation of size at most `2^s`. -/
theorem kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorQuotient
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) :=
  exactVisibleCompressionTarget_iff_finitePredictorQuotient

/-- Route-coverage anchor: clocked exact-visible realization is equivalently a
finite quotient-code presentation of size at most `2^s`. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_finitePredictorQuotient
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) :=
  exists_clockedExactVisibleRealization_iff_finitePredictorQuotient

/-- Route-coverage anchor: finite predictor-image covers can be represented by a
finite list of actual selected indices, and conversely. -/
theorem kpolyCoverage_anchor_finitePredictorCover_iff_finiteIndexRepresentativeCover
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N :=
  IndexedPredictorFamily.finitePredictorCover_iff_finiteIndexRepresentativeCover

/-- Route-coverage anchor: finite predictor-image covers are equivalently
finite quotient-code presentations. -/
theorem kpolyCoverage_anchor_finitePredictorCover_iff_finitePredictorQuotient
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finitePredictorCover_iff_finitePredictorQuotient

/-- Route-coverage anchor: finite representative-index covers are equivalently
finite quotient-code presentations. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_iff_finitePredictorQuotient
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FiniteIndexRepresentativeCover N ↔ G.FinitePredictorQuotient N :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_iff_finitePredictorQuotient

/-- Route-coverage anchor: exact visible compression is equivalently a finite
representative-index cover of size at most `2^s`. -/
theorem kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) :=
  exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover

/-- Route-coverage anchor: clocked exact-visible realization is equivalently a
finite representative-index cover of size at most `2^s`. -/
theorem kpolyCoverage_anchor_clockedRealization_iff_finiteIndexRepresentativeCover
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) :=
  exists_clockedExactVisibleRealization_iff_finiteIndexRepresentativeCover

/-- Route-coverage anchor: nonexistence of a clocked exact-visible realization
is equivalently nonexistence of a finite representative-index cover of size at
most `2^s`. -/
theorem kpolyCoverage_anchor_not_clockedRealization_iff_not_finiteIndexRepresentativeCover
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) :=
  not_exists_clockedExactVisibleRealization_iff_not_finiteIndexRepresentativeCover

/-- Route-coverage anchor: nonexistence of a clocked exact-visible realization
is equivalently nonexistence of a finite quotient-code presentation of size at
most `2^s`. -/
theorem kpolyCoverage_anchor_not_clockedRealization_iff_not_finitePredictorQuotient
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) :=
  not_exists_clockedExactVisibleRealization_iff_not_finitePredictorQuotient

/-- Route-coverage anchor: finite predictor-image covers are stable under
weakening the allowed cover size. -/
theorem kpolyCoverage_anchor_finitePredictorCover_mono
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M :=
  IndexedPredictorFamily.finitePredictorCover_mono hNM hcover

/-- Route-coverage anchor: finite representative-index covers are stable under
weakening the allowed representative count. -/
theorem kpolyCoverage_anchor_finiteIndexRepresentativeCover_mono
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M :=
  IndexedPredictorFamily.finiteIndexRepresentativeCover_mono hNM hrep

/-- Route-coverage anchor: finite quotient-code presentations are stable under
weakening the allowed code count. -/
theorem kpolyCoverage_anchor_finitePredictorQuotient_mono
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M :=
  IndexedPredictorFamily.finitePredictorQuotient_mono hNM hquot
end Mettapedia.Computability.PNP
