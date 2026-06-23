import Mettapedia.Computability.PNP.CruxKpolyCoverageInterfaces
import Mettapedia.Computability.PNP.CruxKpolyActualLocalExactZAB

/-!
# CruxSynthesisRegressionKpolyVisibleClockedPayload

Clocked payload and exact-ZAB payload regressions for visible Kpoly anchors.
-/

namespace Mettapedia.Computability.PNP.CruxSynthesisRegression

open Mettapedia.Computability.PNP
universe u v w z

theorem kpoly_anchor_clocked_realization_iff_finite_predictor_cover_regression
    {Z : Type*} {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    (∃ F : ClockedBitCodeFamily (ExactVisiblePostSwitchSurface Z k) s clock,
        G.RealizedByClockedBitFamily F) ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedRealization_iff_finitePredictorCover

theorem kpoly_anchor_clocked_payload_iff_finite_predictor_cover_regression
    {Z : Type*} [Fintype Z] {k s clock : ℕ} {Index : Type*}
    {G : ExactVisibleSwitchedFamily Z k Index} :
    ClockedKpolyFiniteLearningPayload G s clock ↔
      G.FinitePredictorCover (2 ^ s) := by
  exact kpolyCoverage_anchor_clockedFiniteLearningPayload_iff_finitePredictorCover

theorem kpoly_anchor_exact_zab_erm_clocked_payload_regression
    {Z : Type v} [Fintype Z] {r k clock : ℕ} {Index : Type u}
    (zfeat : Z → BitVec r)
    (samples : Index → Sample (ExactVisiblePostSwitchSurface Z k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (exactZABDecisionListERMFamily
        (Z := Z) (r := r) (k := k) (Index := Index) zfeat samples)
      (r + 2 * k + 1) clock := by
  exact
    kpolyCoverage_anchor_exactZABDecisionListERMClockedKpolyFiniteLearningPayload
      (Z := Z) (r := r) (k := k) (clock := clock) (Index := Index)
      zfeat samples

theorem kpoly_anchor_bitvec_zab_erm_clocked_payload_regression
    {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool) :
    ClockedKpolyFiniteLearningPayload
      (bitVecZABDecisionListERMFamily
        (r := r) (k := k) (Index := Index) samples)
      (r + 2 * k + 1) clock := by
  exact
    kpolyCoverage_anchor_bitVecZABDecisionListERMClockedKpolyFiniteLearningPayload
      (r := r) (k := k) (clock := clock) (Index := Index) samples

theorem kpoly_anchor_clocked_payload_of_eq_bitvec_zab_erm_regression
    {r k clock : ℕ} {Index : Type u} [Fintype (BitVec r)]
    (samples :
      Index → Sample (ExactVisiblePostSwitchSurface (BitVec r) k) Bool)
    {G : ExactVisibleSwitchedFamily (BitVec r) k Index}
    (hG :
      G =
        bitVecZABDecisionListERMFamily
          (r := r) (k := k) (Index := Index) samples) :
    ClockedKpolyFiniteLearningPayload G (r + 2 * k + 1) clock := by
  exact
    kpolyCoverage_anchor_clockedPayload_of_eq_bitVecZABDecisionListERMFamily
      (r := r) (k := k) (clock := clock) (Index := Index) samples hG

theorem kpoly_anchor_current_interface_not_forall_clocked_payload_regression
    {Z : Type v} [Fintype Z] {k s clock : ℕ}
    (hs : s < Fintype.card (ExactVisiblePostSwitchSurface Z k)) :
    ¬ (∀ {Index : Type v} (G : ExactVisibleSwitchedFamily Z k Index),
        ClockedKpolyFiniteLearningPayload G s clock) := by
  exact
    kpolyCoverage_anchor_currentExactVisibleInterface_not_forall_clockedPayload_of_lt_surfaceCard
      (Z := Z) (k := k) (s := s) (clock := clock) hs

end Mettapedia.Computability.PNP.CruxSynthesisRegression
