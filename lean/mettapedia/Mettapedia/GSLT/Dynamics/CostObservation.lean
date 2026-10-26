import Mettapedia.Algebra.WorkSpanInformationLoss
import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.NativeCostLayerReceiptObservation

/-!
# Cost observations of lawful operational schedules

This integration applies the information-loss interface to the maintained
candidate's receipt-retaining schedules. Exact histories determine WorkSpan;
its two certified chronological orders show that WorkSpan does not determine
history. The model makes no native implementation or measurement claim.
-/

namespace Mettapedia.GSLT.Dynamics.CostObservation

open Mettapedia.Algebra Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.LanguageDef.Cost.Layer.Operational
open Mettapedia.GSLT.LanguageDef.CostScheduleObservation
open Mettapedia.Languages.MeTTa.PrimeCandidates.NativeCostLayerReceiptObservation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Existing lawful executions, with their source and target retained. -/
abbrev Execution (Ground : Type*) :=
  Σ source target : CostConfig Ground, OperationalSchedule Ground source target

def cost {Ground : Type*} (execution : Execution Ground) : WorkSpan := execution.2.2.workSpan
def history {Ground : Type*} (execution : Execution Ground) : List (WaveEvent Ground) :=
  Schedule.events execution.2.2

/-- The independently defined history fold computes the schedule's cost. -/
theorem cost_factors_through_history (Ground : Type*) :
    Factors (history : Execution Ground → _) cost :=
  ⟨historyWorkSpan, fun execution => historyWorkSpan_events execution.2.2⟩

/-- The two existing certified schedules spend different first receipts while
performing equal work in equally many chronological waves. -/
def historyCollision : NonTrivialFiber (cost : Execution String → _) history := by
  open Examples in
  exact ⟨⟨_, _, forwardSchedule⟩, ⟨_, _, reverseSchedule⟩,
    two_orders_same_workSpan, two_orders_distinct_histories⟩

/-- Cost recovery from history has no inverse, even on lawful executions. -/
theorem history_does_not_factor_through_cost :
    ¬ Factors (cost : Execution String → _) history :=
  historyCollision.not_factors

end Mettapedia.GSLT.Dynamics.CostObservation
