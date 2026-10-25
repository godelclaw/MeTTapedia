import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceHandoff
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation

/-! # Prepared occurrence matches enter retained conditional execution -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceContinuation

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching GeneralPremise GeneralTypedSites
open Mettapedia.GSLT.LanguageDef WellSorted
open CollectionOccurrenceHandoff RecursiveCollectionHandoff

/-- The declaration index and complete local binder context come from the
licensed occurrence. Local admission and source checks precede scheduling;
capture typing, premises and reduct checking remain in the shared executor. -/
def request? (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (job : Job)
    (valid : job.Valid plan bound expected source)
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (matching : prepared.Valid job.request answer) (depth : Nat) :
    Option RecursiveCollectionContinuation.Request :=
  let environment := GeneralPlanEnvironment.environment plan
  if admitted : admittedFor job.origin.declaration.rule job.origin.declaration.binding.spec then
    if sorted : checkOpenPatternWellSorted environment.language environment.free
        job.variant.site.focusBound job.variant.site.focusType job.variant.site.focus then
      some
        { environment, depth, bound := job.variant.site.focusBound, type := job.variant.site.focusType,
          source := job.variant.site.focus, index := job.origin.ordinal,
          rule := job.origin.declaration.rule, spec := job.origin.declaration.binding.spec,
          answer, prepared, declared := GeneralRuleJobs.Job.selected_rule valid.1,
          specified := GeneralRuleJobs.Job.selected_specification valid.1,
          admitted, sorted := checkOpenPatternWellSorted_sound sorted, matching }
    else none
  else none

/-- Read a completed allocation through the original receipt constructor.
Its declaration, context, allocation history and premise history stay apart. -/
def finish? (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (job : Job) (prepared : Prepared) (firing : Complete.DeepRoot.Firing) :=
  CollectionOccurrenceHandoff.finish? plan bound expected job prepared firing.completed firing.history

/-- Every finished publication is a step of the original presented source
system, including the surrounding typed context. The native continuation
cannot grant a new rule or erase a failed premise. -/
theorem finish_source_step (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (job : Job)
    (valid : job.Valid plan bound expected source)
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (matching : prepared.Valid job.request answer) (depth : Nat)
    {request : RecursiveCollectionContinuation.Request}
    (made : request? plan bound expected source job valid answer prepared matching depth = some request)
    (state : RecursiveCollectionContinuation.State request)
    {firing : Complete.DeepRoot.Firing}
    (published : firing ∈ RecursiveCollectionContinuation.publication request state)
    {receipt : GeneralRuleJobs.Receipt}
    (emitted : finish? plan bound expected job prepared firing = some receipt) :
    (Complete.Presented.gslt plan bound expected).Step source receipt.target := by
  unfold request? at made
  dsimp only at made
  split at made
  · split at made
    · cases Option.some.inj made
      have premises := RecursiveCollectionContinuation.publication_premises _ state published
      apply CollectionOccurrenceHandoff.finish_source_step valid matching _ emitted
      simpa only [RecursiveCollectionContinuation.Request.context,
        GeneralRuleJobs.Job.context, Job.preparedJob, CollectionSelection.refocus] using premises
    · cases made
  · cases made

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceContinuation
