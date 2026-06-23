import Mettapedia.Computability.PNP.CruxKpolyFiniteCoverEquivalences
import Mettapedia.Computability.PNP.CruxKpolyCoverageInterfaces

/-!
# Regression checks for PNP Kpoly finite-cover equivalences

Regression anchors for finite-cover, finite-representative, quotient, clocked-realization, and monotonicity equivalences.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_finitePredictorCover_iff_finiteIndexRepresentativeCover_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N : ℕ} :
    G.FinitePredictorCover N ↔ G.FiniteIndexRepresentativeCover N := by
  exact kpolyCoverage_anchor_finitePredictorCover_iff_finiteIndexRepresentativeCover

theorem kpoly_anchor_exact_visible_compression_target_iff_finitePredictorCover_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorCover

theorem kpoly_anchor_clocked_realization_iff_finitePredictorCover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finitePredictorCover

theorem kpoly_anchor_clocked_finite_learning_payload_iff_finitePredictorCover_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover

theorem kpoly_anchor_clocked_finite_learning_payload_iff_exact_visible_compression_target_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  exact kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_exactVisibleCompressionTarget

theorem kpoly_anchor_exact_visible_compression_target_iff_finitePredictorQuotient_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finitePredictorQuotient

theorem kpoly_anchor_clocked_realization_iff_finitePredictorQuotient_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorQuotient (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finitePredictorQuotient

theorem kpoly_anchor_exact_visible_compression_target_iff_finiteIndexRepresentativeCover_regression
    {Z : Type*} {k s : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact kpolyCoverage_anchor_exactVisibleCompressionTarget_iff_finiteIndexRepresentativeCover

theorem kpoly_anchor_clocked_realization_iff_finiteIndexRepresentativeCover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finiteIndexRepresentativeCover

theorem kpoly_anchor_not_clocked_realization_iff_not_finiteIndexRepresentativeCover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FiniteIndexRepresentativeCover (2 ^ s) := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_iff_not_finiteIndexRepresentativeCover

theorem kpoly_anchor_not_clocked_realization_iff_not_finitePredictorQuotient_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (¬ ∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      ¬ G.FinitePredictorQuotient (2 ^ s) := by
  exact
    kpolyCoverage_anchor_not_clockedRealization_iff_not_finitePredictorQuotient

theorem kpoly_anchor_finitePredictorCover_mono_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hcover : G.FinitePredictorCover N) :
    G.FinitePredictorCover M := by
  exact kpolyCoverage_anchor_finitePredictorCover_mono hNM hcover

theorem kpoly_anchor_finiteIndexRepresentativeCover_mono_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hrep : G.FiniteIndexRepresentativeCover N) :
    G.FiniteIndexRepresentativeCover M := by
  exact kpolyCoverage_anchor_finiteIndexRepresentativeCover_mono hNM hrep

theorem kpoly_anchor_finitePredictorQuotient_mono_regression
    {Index Input : Type*} {G : IndexedPredictorFamily Index Input} {N M : ℕ}
    (hNM : N ≤ M) (hquot : G.FinitePredictorQuotient N) :
    G.FinitePredictorQuotient M := by
  exact kpolyCoverage_anchor_finitePredictorQuotient_mono hNM hquot

end Mettapedia.Computability.PNP.CruxSynthesisRegression
