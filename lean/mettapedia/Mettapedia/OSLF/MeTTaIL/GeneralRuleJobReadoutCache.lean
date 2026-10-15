import Mettapedia.OSLF.MeTTaIL.GeneralRuleJobCoverage
import Mettapedia.Data.List.MemoizedMap

/-!
# Factoring rule readout through its replacement decision

The expensive representation and enclosing-type checks depend on the admitted
request and local target. Matching and premise evidence is reconstructed for
each physical result, including results with the same endpoint. A retained
decision therefore shares checks without sharing or deleting occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.ReadoutCache

open Syntax GeneralRuleJobs
open Mettapedia.GSLT.LanguageDef.WellSorted

def target? (request : Request) (localTarget : Pattern) : Option Pattern :=
  if request.job.site.acceptsReplacementRepresentation request.environment.language localTarget then
    let target := request.job.site.context.fill localTarget
    if checkOpenPatternWellSorted request.environment.language request.environment.free
        request.bound request.expected target then some target else none
  else none

def localTarget {request : Request}
    (result : GeneralPremise.Execution.Result request.environment request.goal) : Pattern :=
  match result with
  | .root _ _ _ _ target _ => target

def reconstruct (request : Request)
    (result : GeneralPremise.Execution.Result request.environment request.goal)
    (target : Option Pattern) : Option Receipt :=
  target.map fun endpoint =>
    match result with
    | .root trace captured completed history localTarget _ =>
        ⟨request.job, trace, captured, completed, history, localTarget, endpoint⟩

/-- The independent executable replacement decision factors the original
proof-carrying projection exactly, including refusal. -/
theorem rootProjection_factor (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (result : GeneralPremise.Execution.Result request.environment request.goal) :
    (rootProjection request licensed result).map Subtype.val =
      reconstruct request result (target? request (localTarget result)) := by
  cases result with
  | root trace captured completed history target valid =>
      unfold rootProjection finishRoot reconstruct target? localTarget
      split
      · split <;> simp_all

/-- Extracting only the target from a checked receipt forgets no part of the
replacement decision. The remaining fields are reconstructed separately. -/
theorem reconstruction_target (request : Request)
    (result : GeneralPremise.Execution.Result request.environment request.goal)
    (target : Option Pattern) :
    (reconstruct request result target).map Receipt.target = target := by
  cases target <;> cases result <;> rfl

def run (request : Request)
    (results : List (GeneralPremise.Execution.Result request.environment request.goal)) :=
  List.MemoizedMap.run localTarget (target? request) (reconstruct request) results none

theorem run_exact (request : Request)
    (licensed : request.job.Valid request.plan request.bound request.expected request.source)
    (results : List (GeneralPremise.Execution.Result request.environment request.goal)) :
    (run request results).1 =
      results.map (fun result => (rootProjection request licensed result).map Subtype.val) := by
  rw [run, (List.MemoizedMap.run_exact localTarget (target? request)
    (reconstruct request) results none (List.MemoizedMap.valid_none _)).1]
  apply List.map_congr_left
  intro result _
  exact (rootProjection_factor request licensed result).symm

theorem run_calls_bound (request : Request)
    (results : List (GeneralPremise.Execution.Result request.environment request.goal)) :
    (run request results).2.2 ≤ results.length :=
  List.MemoizedMap.calls_le_length _ _ _ _ _

/-- Different derivation evidence sharing one local target takes one decision
call while retaining both original results. -/
theorem two_equal_targets_share (request : Request)
    (first second : GeneralPremise.Execution.Result request.environment request.goal)
    (same : localTarget first = localTarget second) :
    (run request [first, second]).2.2 = 1 :=
  List.MemoizedMap.adjacent_same_key_calls _ _ _ first second same

theorem reconstruction_retains_evidence (request : Request)
    (trace : List GeneralScopedMatchMachine.BagChoice)
    (captured completed : ScopedRuleMatching.Assignment)
    (history : List GeneralPremise.Event) (localTarget target : Pattern)
    (valid : GeneralPremise.RootFiring request.environment request.job.site.focusBound
      request.job.site.focusType request.job.site.focus request.job.ordinal trace captured completed history localTarget) :
    reconstruct request (.root trace captured completed history localTarget valid) (some target) =
      some ⟨request.job, trace, captured, completed, history, localTarget, target⟩ := rfl

end Mettapedia.OSLF.MeTTaIL.GeneralRuleJobExecution.ReadoutCache
