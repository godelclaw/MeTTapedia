import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceMachineExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRequestPrimitives
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Steps

/-!
# Native discovery of retained collection matcher lanes

The discovery component reuses typed rule-job enumeration and residual-context
variants. Its runtime extends the checked joint machine with the existing
context operations once. It neither selects an emission profile nor changes
source admission.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax
open CollectionOccurrenceHandoff CollectionOccurrenceMatcher
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit
open CollectionOccurrenceRuntime
open scoped ProgramQuotation

def contexts : Library :=
  ⟨CollectionOccurrenceMachineExecution.library.runtime,
    CollectionContextExecution.source.program, ["gslt:collection-context:"]⟩

theorem contexts_checked : contexts.check = true := by decide +kernel

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_occurrence_discovery.metta"
    sha256 "e9a6245831dd80046f26c38e13509251840c3c5c4a6d7c5460e1fdab76fadcdc"

def library : Library :=
  ⟨contexts.runtime, source.program, ["gslt:occurrence-discovery:"]⟩

theorem checked : library.check = true := by decide +kernel

/-- The context traversal calls only its own operations and these existing
scoped/list primitives. Inert data constructors remain outside the runtime
function namespace. -/
def contextHeads (head : String) : Bool :=
  !"gslt:".isPrefixOf head || "gslt:collection-context:".isPrefixOf head ||
    ["gslt:automata:append", "gslt:automata:length",
      "gslt:rule:scope-fill", "gslt:rule:scope-match-erase-at"].contains head

theorem context_closed : ProgramClosed contextHeads CollectionContextExecution.library.runtime := by
  apply closed_of_all _ _ (by decide +kernel)
  decide +kernel

private def equationData (equation : SpaceSemantics.Equation) : String × List Atom × Atom :=
  (equation.head, equation.arguments, equation.body)

private theorem equationData_injective : Function.Injective equationData := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ same
  simp only [equationData, Prod.mk.injEq] at same
  rcases same with ⟨rfl, rfl, rfl⟩
  rfl

theorem context_agreement :
    ProgramAgreementOn contextHeads CollectionContextExecution.library.runtime contexts.runtime := by
  apply programAgreementOn_of_retained_rows
  · apply (List.map_inj_right (fun _ _ same => equationData_injective same)).mp
    decide +kernel
  · decide +kernel

syntax "discovery_from_matcher% " "[" str,* "] " term:max : term
macro_rules
  | `(discovery_from_matcher% [$names,*] $fact) =>
    `(by
      have atRuntime := occurrence_from_matcher% [$names,*] $fact
      have atCollector := by
        metta_lift CollectionOccurrenceCollectorExecution.checked [$names,*] atRuntime
      have atMachine := by
        metta_lift CollectionOccurrenceMachineExecution.checked [$names,*] atCollector
      have atContexts := by metta_lift contexts_checked [$names,*] atMachine
      metta_lift checked [$names,*] atContexts)

syntax "discovery_from_context% " "[" str,* "] " term:max : term
macro_rules
  | `(discovery_from_context% [$names,*] $fact) =>
    `(by
      have atContexts := BridgeKit.transport_call context_closed context_agreement
        (by decide +kernel) (by decide) (by decide +kernel) (by decide)
        [$names,*] (by decide) (by rfl) (by decide +kernel) $fact
      metta_lift checked [$names,*] atContexts)

def begunTerm (job : Job) : Term :=
  .application "RecursiveOccurrenceLane"
    [CollectionOccurrenceMatcherExecution.originTerm job,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request,
      RecursiveCollectionExecution.stateTerm (RecursiveCollectionMachine.start job.request), .natural 0]

/-- Starting a wire job requires no supplied validity proof. Licensing is
established by typed job discovery before these lanes enter the source search. -/
theorem begin_job_returns (host : Effects.State) (job : Job) :
    PureReturns CollectionOccurrenceMatcherExecution.library.runtime [] host
      (apply "gslt:occurrence-matcher:begin"
        [encoded (CollectionOccurrenceMatcherExecution.originTerm job),
          encoded (RuleInstantiationExecution.GeneralExecution.matcherRequestTerm job.request)])
      host (encoded (begunTerm job)) := by
  have native := RecursiveCollectionExecution.start_returns host job.request
  have begun := by metta_lift CollectionOccurrenceMatcherExecution.checked ["request"] native
  occurrence_matcher_eval [begun] unfolding [begunTerm]

syntax "discovery_from_complete% " "[" str,* "] " term:max : term
macro_rules
  | `(discovery_from_complete% [$names,*] $fact) =>
    `(by
      have atBase := by
        metta_lift CollectionMatcherBackendExecution.collectionBase_checked [$names,*] $fact
      have atBackend := by
        metta_lift CollectionMatcherBackendExecution.checked [$names,*] atBase
      have atContinuation := by
        metta_lift RecursiveCollectionContinuationExecution.checked [$names,*] atBackend
      have atBatch := by
        metta_lift CollectionOccurrenceBatchExecution.checked [$names,*] atContinuation
      have atInstallation := by
        metta_lift CollectionOccurrenceInstallationExecution.checked [$names,*] atBatch
      have atMachine := machine_from_publication% [$names,*] atInstallation
      have atContexts := by metta_lift contexts_checked [$names,*] atMachine
      metta_lift checked [$names,*] atContexts)

private theorem elaborated_types_returns (host : Effects.State)
    (types : List (String × TypeExpr)) (origin : GeneralRuleBindingInference.Origin) :
    PureReturns library.runtime [] host
      (apply "gslt:collection-search:elaborated-types"
        [encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm types),
          encoded (ScopedRuleJobReadoutExecution.originTerm origin)])
      host (encoded (encodeList InferenceCettaWire.AuthoredRule.typeBindingTerm
        (CollectionRequestExecution.elaboratedTypeContext types origin))) := by
  have atRecursive := recursive_from_logged% ["types", "origin"]
    (CollectionRequestExecution.elaborated_types_returns host types origin)
  have atMatcher := by
    metta_lift CollectionOccurrenceMatcherExecution.checked ["types", "origin"] atRecursive
  exact discovery_from_matcher% ["types", "origin"] atMatcher

syntax "discovery_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| discovery_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

@[metta_head "gslt:occurrence-discovery:variant"]
theorem variant_returns (host : Effects.State) (origin : GeneralRuleJobs.Job)
    (variant : CollectionSelection.SiteVariant) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-discovery:variant"
        [encoded (ScopedRuleJobReadoutExecution.jobTerm origin),
          encoded (CollectionContextExecution.variantTerm variant)])
      host (encoded (begunTerm ⟨origin, variant⟩)) := by
  have elaborated := elaborated_types_returns host origin.declaration.authored.typeContext
    origin.declaration.binding.origin
  rw [CollectionRequestExecution.elaboratedTypeContext_eq
    origin.declaration.authored.typeContext origin.declaration.binding.spec
    origin.declaration.binding.origin] at elaborated
  have counted := discovery_from_complete% ["items"]
    (CompleteExecution.complete_length_returns InferenceCettaWire.AuthoredRule.typeTerm
      host variant.site.focusBound)
  have begun := discovery_from_matcher% ["origin", "query"]
    (begin_job_returns host ⟨origin, variant⟩)
  simp only [CollectionOccurrenceMatcherExecution.originTerm, Job.request,
    RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
    GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate,
    InferenceCettaWire.AuthoredRule.rewriteTerm,
    InferenceCettaWire.AuthoredRule.optionalBindingTerm] at begun
  have emptyBindings :
      CettaWireAtom.encode (MatchAutomataBindingExecution.payloadBindingsTerm []) =
        Atom.symbol "LNil" := rfl
  discovery_eval [elaborated, counted, begun] unfolding
    [ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.rulePlanTerm,
      ScopedRuleJobReadoutExecution.bindingPlanTerm, ScopedRuleJobReadoutExecution.siteTerm,
      CollectionContextExecution.variantTerm, InferenceCettaWire.AuthoredRule.rewriteTerm,
      CollectionOccurrenceMatcherExecution.originTerm, Job.request,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      GeneralExecutionAdmission.RulePlan.rule, GeneralRuleBindingInference.BindingPlan.elaborate,
      CollectionRequestExecution.elaboratedTypeContext_eq,
      InferenceCettaWire.AuthoredRule.optionalBindingTerm,
      encodeList, InferenceCettaWire.encodeList]
  metta_capture_any begun unfolding
    [ScopedRuleJobReadoutExecution.jobTerm, ScopedRuleJobReadoutExecution.rulePlanTerm,
      ScopedRuleJobReadoutExecution.bindingPlanTerm, ScopedRuleJobReadoutExecution.siteTerm,
      CollectionContextExecution.variantTerm, InferenceCettaWire.AuthoredRule.rewriteTerm,
      InferenceCettaWire.AuthoredRule.optionalBindingTerm,
      InferenceCettaWire.AuthoredRule.siteTerm,
      RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      GeneralRuleBindingInference.BindingPlan.implicitTypes,
      encodeList, InferenceCettaWire.encodeList, emptyBindings]

@[metta_head "gslt:occurrence-discovery:variants"]
theorem variants_returns (host : Effects.State) (origin : GeneralRuleJobs.Job) :
    ∀ variants : List CollectionSelection.SiteVariant,
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-discovery:variants"
        [encoded (ScopedRuleJobReadoutExecution.jobTerm origin),
          encoded (encodeList CollectionContextExecution.variantTerm variants)])
      host (encoded (encodeList (fun variant => begunTerm ⟨origin, variant⟩) variants))
  | [] => by discovery_eval unfolding [encodeList]
  | variant :: variants => by
    have first := variant_returns host origin variant
    have later := variants_returns host origin variants
    discovery_eval [first, later] unfolding [encodeList]

private theorem append_returns (host : Effects.State) (first rest : List Job) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:append"
        [encoded (encodeList begunTerm first), encoded (encodeList begunTerm rest)])
      host (encoded (encodeList begunTerm (first ++ rest))) := by
  exact discovery_from_complete% ["left", "right"]
    (CompleteExecution.complete_append_returns begunTerm host first rest)

@[metta_head "gslt:occurrence-discovery:jobs"]
theorem jobs_returns (host : Effects.State) :
    ∀ origins : List GeneralRuleJobs.Job,
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-discovery:jobs"
        [encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm origins)])
      host (encoded (encodeList begunTerm (origins.flatMap fun origin =>
        (CollectionSelection.siteVariants origin.site).map fun variant => ⟨origin, variant⟩)))
  | [] => by discovery_eval unfolding [encodeList]
  | origin :: origins => by
    have variants := discovery_from_context% ["site"]
      (CollectionContextExecution.site_variants_returns host origin.site)
    have first := variants_returns host origin (CollectionSelection.siteVariants origin.site)
    have later := jobs_returns host origins
    have appended := append_returns host
      ((CollectionSelection.siteVariants origin.site).map fun variant => ⟨origin, variant⟩)
      (origins.flatMap fun origin =>
        (CollectionSelection.siteVariants origin.site).map fun variant => ⟨origin, variant⟩)
    simp only [encodeList_map, Function.comp_def] at appended
    discovery_eval [variants, first, later, appended] unfolding
      [ScopedRuleJobReadoutExecution.jobTerm, List.flatMap_cons, encodeList_map, Function.comp_def]

theorem lanes_encoding (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr)
    (expected : TypeExpr) (subject : Pattern) :
    encodeList CollectionOccurrenceMatcherExecution.laneTerm (lanes plan bound expected subject) =
      encodeList begunTerm (CollectionOccurrenceHandoff.jobs plan bound expected subject) := by
  simp only [lanes, encodeList_map]
  change encodeList (fun selected => begunTerm selected.val)
    (CollectionOccurrenceHandoff.jobs plan bound expected subject).attach = _
  calc
    _ = encodeList begunTerm
        ((CollectionOccurrenceHandoff.jobs plan bound expected subject).attach.map Subtype.val) :=
      (encodeList_map begunTerm Subtype.val
        (CollectionOccurrenceHandoff.jobs plan bound expected subject).attach).symm
    _ = _ := congrArg (encodeList begunTerm) (List.attach_map_subtype_val _)

/-- The native factory discovers the actual typed jobs of its current source,
expands their residual contexts, and initializes precisely the retained joint
machine. The caller supplies only the finite free-context projection needed
by the existing typed-site generator. -/
@[metta_head "gslt:occurrence-discovery:begin"]
theorem begin_returns (host : Effects.State) (plan : GeneralExecutionAdmission.Plan)
    (bound : List TypeExpr) (expected : TypeExpr) (subject : Pattern)
    (footprint : List String) (covered : ∀ name ∈ subject.freeFvarNames, name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-discovery:begin"
        [encoded (PremiseOperationsExecution.DeclarationTyping.declarationsTerm
            (GeneralPlanEnvironment.environment plan).language.terms),
          encoded (PremiseOperationsExecution.DeclarationTyping.freeContextTerm
            (plan.snapshot.free.entriesOn footprint)),
          encoded (InferenceCettaWire.ContextObservation.permissionsTerm plan.permissions.sites),
          encoded (PremiseOperationsExecution.DeclarationTyping.boundContextTerm bound),
          encoded (InferenceCettaWire.AuthoredRule.typeTerm expected),
          encoded (InferenceCettaWire.encodePattern subject),
          encoded (encodeList ScopedRuleJobReadoutExecution.rulePlanTerm plan.rules)])
      host (encoded (CollectionOccurrenceMachineExecution.stateTerm
        (CollectionOccurrenceMachine.begin plan bound expected subject))) := by
  have generated := discovery_from_complete%
    ["declarations", "free", "permissions", "bound", "expected", "source", "rules"]
    (CompleteExecution.complete_jobs_returns host plan bound expected subject footprint covered)
  have discovered := jobs_returns host (GeneralRuleJobs.jobs plan bound expected subject)
  have initial := CollectionOccurrenceMachineExecution.from_lanes_returns
    (plan := plan) (bound := bound) (expected := expected) (sourcePattern := subject) host
  have atContexts := by metta_lift contexts_checked ["lanes"] initial
  have started := by metta_lift checked ["lanes"] atContexts
  rw [lanes_encoding] at started
  discovery_eval [generated, discovered, started] unfolding [CollectionOccurrenceHandoff.jobs]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceDiscoveryExecution
