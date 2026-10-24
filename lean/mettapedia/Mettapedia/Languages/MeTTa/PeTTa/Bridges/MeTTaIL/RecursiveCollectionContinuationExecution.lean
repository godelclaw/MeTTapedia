import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContinuationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionHandoffExecution
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionContinuation

/-!
# Native retained continuations for recursive collection allocations

The wire frame retains the prepared source, original allocation history and
shared scheduled premise state. Its operations use the established post-match
continuation and descent machine at the actual complete binder context.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RecursiveCollectionContinuation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open CompleteExecution.DescentCodec
open RecursiveCollectionHandoffExecution (preparedTerm)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_continuation.metta"
    sha256 "9e633218ef92c971c475a1ffbcf43a8c319d277f513f5a0a155426e99e56f86f"

def library : BridgeKit.Library :=
  ⟨CollectionMatcherBackendExecution.library.runtime, source.program,
    ["gslt:collection-continuation:"]⟩

theorem checked : library.check = true := by decide +kernel

def frameTerm (request : Request) (search : State request) : Term :=
  .application "RecursiveCollectionContinuation" [preparedTerm request.prepared, stateTerm search]

def publicationTerm (request : Request) (firing : Complete.DeepRoot.Firing) : Term :=
  .application "RecursiveCollectionContinued" [preparedTerm request.prepared, CompleteExecution.firingTerm firing]

syntax "recursive_continuation_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| recursive_continuation_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call checked; metta_eval [$facts,*] with checked
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        frameTerm, publicationTerm, preparedTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, $extra,*]))

@[metta_head "gslt:collection-continuation:begin"]
theorem begin_returns (host : Effects.State) (request : Request) (footprint : List String)
    (inside : ∀ name ∈ request.source.freeFvarNames, name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:begin"
        [CompleteExecution.environmentValue request.environment (request.environment.free.entriesOn footprint),
          number request.depth, encoded (typesTerm request.bound), encoded (typeTerm request.type),
          number request.index, encoded (InferenceCettaWire.AuthoredRule.rewriteTerm request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm request.spec),
          encoded (preparedTerm request.prepared)])
      host (encoded (frameTerm request (RecursiveCollectionContinuation.start request))) := by
  have atDescent := CompleteExecution.descent_continue_root_answer_returns host
    request.environment footprint request.depth request.bound request.type request.prepared.source
    request.index request.rule request.spec request.declared request.specified request.admitted
    request.sourceTyped request.prepared.ordinary request.matching.matching
    (captures_free_within request footprint inside) (.done request.goal) []
  have atComplete := by
    metta_lift CompleteExecution.complete_checked
      ["environment", "depth", "bound", "type", "source", "index", "rule", "spec", "answer", "tail", "next"] atDescent
  have atBase := by
    metta_lift CollectionMatcherBackendExecution.collectionBase_checked
      ["environment", "depth", "bound", "type", "source", "index", "rule", "spec", "answer", "tail", "next"] atComplete
  have atBackend := by
    metta_lift CollectionMatcherBackendExecution.checked
      ["environment", "depth", "bound", "type", "source", "index", "rule", "spec", "answer", "tail", "next"] atBase
  have continued := by
    metta_lift checked
      ["environment", "depth", "bound", "type", "source", "index", "rule", "spec", "answer", "tail", "next"] atBackend
  have expandedAtBackend := CollectionMatcherBackendExecution.expansion_state_returns host request.expansion
  have expanded := by
    metta_lift checked ["expanded"] expandedAtBackend
  recursive_continuation_eval [continued, expanded] unfolding
    [RecursiveCollectionContinuation.start, Request.expansion, Request.goal, CollectionMatcherBackendExecution.expansionState,
      CompleteExecution.matcher_answer_term,
      goalTerm, continuationTerm, typesTerm, typeTerm, patternTerm,
      PremiseOperationsExecution.GeneralExecution.Base.typesTerm,
      encodeList, InferenceCettaWire.encodeList]

private theorem descent_returns (host : Effects.State) (request : Request)
    (footprint : List String) (finiteProvider : request.environment.provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames request.environment.provider, name ∈ footprint)
    (search : State request) (work : Nat)
    (covered : StructuralDescent.Scheduled.stateFreeWithin footprint request.environment request.goal search) :
    PureReturns library.runtime [] host
      (apply "gslt:descent:run"
        [CompleteExecution.environmentValue request.environment (request.environment.free.entriesOn footprint),
          number work, encoded (stateTerm search)])
      host (encoded (stateTerm (run request work search))) := by
  have native := CompleteExecution.descent_run_returns host request.environment finiteProvider
    footprint provider request.goal work search covered
  have atComplete := by
    metta_lift CompleteExecution.complete_checked ["environment", "fuel", "state"] native
  have atBase := by
    metta_lift CollectionMatcherBackendExecution.collectionBase_checked ["environment", "fuel", "state"] atComplete
  have atBackend := by
    metta_lift CollectionMatcherBackendExecution.checked ["environment", "fuel", "state"] atBase
  metta_lift checked ["environment", "fuel", "state"] atBackend

@[metta_head "gslt:collection-continuation:run"]
theorem run_returns (host : Effects.State) (request : Request) (footprint : List String)
    (finiteProvider : request.environment.provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames request.environment.provider, name ∈ footprint)
    (search : State request) (work : Nat)
    (covered : StructuralDescent.Scheduled.stateFreeWithin footprint request.environment request.goal search) :
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:run"
        [CompleteExecution.environmentValue request.environment (request.environment.free.entriesOn footprint),
          number work, encoded (frameTerm request search)])
      host (encoded (frameTerm request (run request work search))) := by
  have native := descent_returns host request footprint finiteProvider provider search work covered
  recursive_continuation_eval [native]

@[metta_head "gslt:collection-continuation:results"]
theorem results_returns (host : Effects.State) (request : Request) :
    ∀ results : List (StructuralDescent.Scheduled.Result request.environment request.goal),
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:results"
        [encoded (preparedTerm request.prepared),
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.prepared.ordinary.assignment),
          encoded (encodeList resultTerm results)])
      host (encoded (encodeList (publicationTerm request) (results.filterMap (read? request))))
  | [] => by recursive_continuation_eval
  | result :: rest => by
    have later := results_returns host request rest
    cases result with
    | root trace captured completed history target held =>
      by_cases same : captured = request.prepared.ordinary.assignment
      · simp only [List.filterMap_cons, RecursiveCollectionContinuation.read?, Complete.DeepRoot.read,
          same, beq_self_eq_true, ↓reduceIte]
        recursive_continuation_eval [later] unfolding
          [read?, Complete.DeepRoot.read, CompleteExecution.firingTerm, resultTerm, answerTerm,
            same, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff, encodeList]
      · have wireNe : RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm captured ≠
            RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm request.prepared.ordinary.assignment :=
          fun equal => same (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective equal)
        simp only [List.filterMap_cons, RecursiveCollectionContinuation.read?, Complete.DeepRoot.read,
          show (captured == request.prepared.ordinary.assignment) = false from beq_eq_false_iff_ne.mpr same,
          Bool.false_eq_true, ↓reduceIte]
        recursive_continuation_eval [later] unfolding
          [read?, Complete.DeepRoot.read, CompleteExecution.firingTerm, resultTerm, answerTerm,
            same, wireNe, RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm_injective.eq_iff, encodeList]

@[metta_head "gslt:collection-continuation:publication"]
theorem publication_returns (host : Effects.State) (request : Request) (search : State request) :
    PureReturns library.runtime [] host
      (apply "gslt:collection-continuation:publication" [encoded (frameTerm request search)])
      host (encoded (encodeList (publicationTerm request) (publication request search))) := by
  have published := results_returns host request search.answers
  recursive_continuation_eval [published] unfolding
    [publication, stateTerm, PremiseSchedulerExecution.schedulerStateTerm,
      CompleteExecution.matcher_answer_term]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution
