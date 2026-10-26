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
      simpa only [GeneralPlanEnvironment.environmentWith_empty, RecursiveCollectionContinuation.Request.context,
        GeneralRuleJobs.Job.context, Job.preparedJob, CollectionSelection.refocus] using premises
    · cases made
  · cases made


namespace Canonical

/-- Every generated focus of the actual normalized source is itself canonical.
Retained-copy variants alter the context, not the focused object. -/
theorem job_target_canonical {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (job : Job)
    (licensed : job.Valid plan bound expected (CanonicalBags.canon source)) :
    CanonicalBags.canon job.request.target = job.request.target := by
  have focused : job.variant.site.focus = job.origin.site.focus := by
    obtain ⟨context, _, same⟩ := List.mem_map.mp licensed.2
    rw [← same]
    rfl
  change CanonicalBags.canon job.variant.site.focus = job.variant.site.focus
  rw [focused]
  apply RecursiveCollectionContinuation.Canonical.focus_canonical job.origin.site.context
  rw [licensed.1.2.source_eq]
  exact CanonicalBags.canon_idempotent source

/-- Local admission constructs the same request; its retained original
allocation proof justifies the canonical seed at the prepared source. -/
theorem request_seed {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (job : Job)
    (licensed : job.Valid plan bound expected (CanonicalBags.canon source))
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (matching : prepared.Valid job.request answer) (depth : Nat)
    {request : RecursiveCollectionContinuation.Request}
    (issued : request? plan bound expected (CanonicalBags.canon source) job licensed
      answer prepared matching depth = some request) :
    canonicalMatchingInterpretation.Matches
      ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
        request.rule.left, request.prepared.source⟩ request.answer.trace request.answer.assignment := by
  have seed := RecursiveCollectionContinuation.Canonical.prepared_seed matching
    (job_target_canonical job licensed)
  unfold request? at issued
  dsimp only at issued
  split at issued
  · split at issued
    · cases Option.some.inj issued
      simpa only [Job.request] using seed
    · cases issued
  · cases issued

/-- The concrete producer path supplies every seed obligation from the actual
published allocation and actual preparation result. No premise outcome or
replacement allocation trace is supplied. -/
theorem published_request_seed {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (job : Job)
    (licensed : job.Valid plan bound expected (CanonicalBags.canon source))
    (work : Nat) (answer : RecursiveCollectionMachine.Answer)
    (published : answer ∈ (RecursiveCollectionMachine.run job.request work
      (RecursiveCollectionMachine.start job.request)).answers)
    (prepared : Prepared) (made : prepare job.request answer = some prepared) (depth : Nat)
    {request : RecursiveCollectionContinuation.Request}
    (issued : request? plan bound expected (CanonicalBags.canon source) job licensed answer prepared
      (prepare_valid job.request answer
        (RecursiveCollectionMachine.published_trace_valid job.request work published) made) depth = some request) :
    request.answer = answer ∧ request.prepared = prepared ∧
      EquationalScopedReceipts.Matches literalBodyComparison job.request.rule job.request.spec
        job.request.ambient job.request.site job.request.path job.request.depth job.request.initial
        job.request.schema job.request.target request.answer.trace request.answer.assignment ∧
      canonicalMatchingInterpretation.Matches
        ⟨request.rule, request.spec, request.bound.length, .left, [], 0, [],
          request.rule.left, request.prepared.source⟩ request.answer.trace request.answer.assignment := by
  have original := RecursiveCollectionMachine.published_trace_valid job.request work published
  have seed := request_seed job licensed answer prepared (prepare_valid job.request answer original made)
    depth issued
  unfold request? at issued
  dsimp only at issued
  split at issued
  · split at issued
    · cases Option.some.inj issued
      exact ⟨rfl, rfl, original, seed⟩
    · cases issued
  · cases issued

/-- The shared inert finisher receives the fixed original allocation trace.
The ordinary finisher continues to select its prepared ordinary trace. -/
def finish? (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (expected : TypeExpr)
    (job : Job) (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (firing : RecursiveCollectionContinuation.Canonical.Firing) :
    Option (GeneralRuleJobs.Receipt EquationalScopedReceipts.Event) :=
  GeneralRuleJobs.finish? plan bound expected (job.preparedJob prepared)
    answer.trace answer.assignment firing.completed firing.history

/-- The receipt retains the fixed seed and the complete actual continuation
history, independently of the root validation trace in the supplied outcome. -/
theorem finish_payload {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {job : Job} {answer : RecursiveCollectionMachine.Answer} {prepared : Prepared}
    {firing : RecursiveCollectionContinuation.Canonical.Firing}
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (emitted : finish? plan bound expected job answer prepared firing = some receipt) :
    receipt.job = job.preparedJob prepared ∧ receipt.matcherTrace = answer.trace ∧
      receipt.captured = answer.assignment ∧ receipt.completed = firing.completed ∧
      receipt.premiseHistory = firing.history := by
  unfold finish? GeneralRuleJobs.finish? GeneralRuleJobs.finishWith? at emitted
  dsimp only at emitted
  split at emitted
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at emitted
    obtain ⟨localTarget, reduced, emitted⟩ := emitted
    split at emitted
    · cases Option.some.inj emitted
      exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · cases emitted
  · cases emitted

/-- Actual published conditional execution licenses the emitted receipt in
the selected interpretation at the licensed prepared source presentation. -/
theorem finish_valid {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (job : Job)
    (licensed : job.Valid plan bound expected (CanonicalBags.canon source))
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (matching : prepared.Valid job.request answer) (depth : Nat)
    {request : RecursiveCollectionContinuation.Request}
    (issued : request? plan bound expected (CanonicalBags.canon source) job licensed
      answer prepared matching depth = some request)
    (state : RecursiveCollectionContinuation.Canonical.State request)
    {firing : RecursiveCollectionContinuation.Canonical.Firing}
    (published : firing ∈ RecursiveCollectionContinuation.Canonical.publication request state)
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (emitted : finish? plan bound expected job answer prepared firing = some receipt) :
    receipt.ValidInWith canonicalMatchingInterpretation DynamicProvider.empty plan bound expected
      (job.presentedSource prepared) := by
  have seed := request_seed job licensed answer prepared matching depth issued
  unfold request? at issued
  dsimp only at issued
  split at issued
  · split at issued
    · cases Option.some.inj issued
      have premises := RecursiveCollectionContinuation.Canonical.publication_premises _ state published
      apply GeneralRuleJobs.finishWith_interpreted_sound (job.prepared_valid licensed matching)
        seed ?_ emitted
      simpa only [GeneralPlanEnvironment.environmentWith_empty, RecursiveCollectionContinuation.Request.context,
        GeneralRuleJobs.Job.context, Job.preparedJob, CollectionSelection.refocus] using premises
    · cases issued
  · cases issued

/-- The prepared receipt remains linked to its actual authored source.
Reference-step agreement is a separate equation/premise transport boundary. -/
theorem finish_original_source {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (job : Job)
    (licensed : job.Valid plan bound expected (CanonicalBags.canon source))
    (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
    (matching : prepared.Valid job.request answer) (depth : Nat)
    {request : RecursiveCollectionContinuation.Request}
    (issued : request? plan bound expected (CanonicalBags.canon source) job licensed
      answer prepared matching depth = some request)
    (state : RecursiveCollectionContinuation.Canonical.State request)
    {firing : RecursiveCollectionContinuation.Canonical.Firing}
    (published : firing ∈ RecursiveCollectionContinuation.Canonical.publication request state)
    {receipt : GeneralRuleJobs.Receipt EquationalScopedReceipts.Event}
    (emitted : finish? plan bound expected job answer prepared firing = some receipt) :
    receipt.ValidInWith canonicalMatchingInterpretation DynamicProvider.empty plan bound expected
      (job.presentedSource prepared) ∧ CanonicalBags.Same source (job.presentedSource prepared) := by
  refine ⟨finish_valid job licensed answer prepared matching depth issued state published emitted, ?_⟩
  exact (show CanonicalBags.Same source (CanonicalBags.canon source) from
    (CanonicalBags.canon_idempotent source).symm).trans (job.source_same licensed matching)

#print axioms finish_payload
#print axioms finish_valid
#print axioms finish_original_source

#print axioms job_target_canonical
#print axioms request_seed
#print axioms published_request_seed

end Canonical

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceContinuation
