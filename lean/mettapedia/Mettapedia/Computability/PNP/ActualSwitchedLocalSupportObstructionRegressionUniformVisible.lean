import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportTransfer
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportAdaptive
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportFullRule
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportCardinality
import Mettapedia.Computability.PNP.ActualSwitchedLocalSupportOneBlock

/-!
# Uniform visible-section regression checks for the actual-local support obstruction
-/

namespace Mettapedia.Computability.PNP

universe v

section UniformVisibleSection

variable {Z : Type v} {Block Index : Type*} {k N s clock : ℕ}
variable (T : ActualSwitchedLocalInterface Z k Index Block)
variable {sec : ExactVisiblePostSwitchSurface Z k → Block}

theorem regression_uniformVisibleSection_factorsThrough_outputFamily
    (hsec : T.HasUniformVisibleSection sec) :
    T.predictorFamily.FactorsThrough sec T.outputFamily := by
  exact
    T.predictorFamily_factorsThrough_outputFamily_of_uniformVisibleSection hsec

theorem regression_uniformVisibleSection_transfers_finite_cover
    (hsec : T.HasUniformVisibleSection sec)
    (hcover : T.outputFamily.FinitePredictorCover N) :
    T.predictorFamily.FinitePredictorCover N := by
  exact
    T.predictorFamily_finitePredictorCover_of_outputFamily_finitePredictorCover
      hsec hcover

theorem regression_uniformVisibleSection_transfers_bit_budget
    (hsec : T.HasUniformVisibleSection sec)
    (hbudget : T.outputFamily.HasBitBudget s) :
    T.predictorFamily.HasBitBudget s := by
  exact
    T.predictorFamily_hasBitBudget_of_outputFamily_hasBitBudget hsec hbudget

theorem regression_uniformVisibleSection_transfers_clocked_payload
    [Fintype Z]
    (hsec : T.HasUniformVisibleSection sec)
    (hbudget : T.outputFamily.HasBitBudget s) :
    ClockedKpolyFiniteLearningPayload T.predictorFamily s clock := by
  exact
    T.clockedKpolyFiniteLearningPayload_of_outputFamily_hasBitBudget
      hsec hbudget

end UniformVisibleSection

end Mettapedia.Computability.PNP
