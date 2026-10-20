import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedRuleInstantiationExecution

/-! Instantiated authored targets for checked collection receipts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionFiringExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax ScopedCollectionMachine
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Effects (State)
open Eval BridgeKit WireKit
open ScopedCollectionExecution

private abbrev a (head : String) (arguments : List Atom) : Atom :=
  .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

theorem scopedInstantiation_agreement :
    ProgramAgreementOn ScopedInstantiationExecution.executionHeads
      ScopedInstantiationExecution.runtime CollectionSelectionExecution.scopedLibrary.runtime := by
  apply programAgreementOn_of_retained_rows
  · rfl
  · rfl

private def operationArities : List (String × Nat) :=
  [("gslt:rule:scope-reduct", 5)]

private theorem raw_at (head : String) (arity index : Nat)
    (member : (head, arity) ∈ operationArities) (bound : index < arity) :
    argumentIsRaw CollectionSelectionExecution.scopedLibrary.runtime head index = true := by
  have checked : operationArities.all (fun operation =>
      (List.range operation.2).all
        (argumentIsRaw CollectionSelectionExecution.scopedLibrary.runtime operation.1)) = true := by rfl
  exact List.all_eq_true.mp (List.all_eq_true.mp checked (head, arity) member)
    index (List.mem_range.mpr bound)

private theorem raw_arguments (head : String) (arity : Nat)
    (member : (head, arity) ∈ operationArities) (arguments : List Atom)
    (length : arguments.length = arity) :
    ∀ index argument, arguments[index]? = some argument →
      argumentIsRaw CollectionSelectionExecution.scopedLibrary.runtime head index = true ∨
        passiveArgument argument = true := by
  intro index argument picked
  exact .inl (raw_at head arity index member (by
    have bound := (List.getElem?_eq_some_iff.mp picked).1
    simpa only [length] using bound))

private theorem ordinary_dispatch (head : String) (arity : Nat)
    (member : (head, arity) ∈ operationArities) :
    (ioHead head || StdLib.known head ||
      CollectionSelectionExecution.scopedLibrary.runtime.equations.any (·.head == head)) = true := by
  have checked : operationArities.all (fun operation =>
      ioHead operation.1 || StdLib.known operation.1 ||
        CollectionSelectionExecution.scopedLibrary.runtime.equations.any
          (·.head == operation.1)) = true := by rfl
  exact List.all_eq_true.mp checked (head, arity) member

theorem scoped_reduct_returns (state : Effects.State) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient : Nat) (assignment : ScopedRuleMatching.Assignment) :
    PureReturns CollectionSelectionExecution.scopedLibrary.runtime [] state
      (apply "gslt:rule:scope-reduct"
        [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient,
          encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)])
      state (encoded (MatchAutomataBindingExecution.patternOptionTerm
        (ScopedRuleMatching.reduct? rule spec ambient assignment))) := by
  let capturedCaller : Subst :=
    [("one", .symbol "None"),
      ("two", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule)),
      ("three", encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec)),
      ("four", number ambient),
      ("five", encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment))]
  have capturedNames : [v "one", v "two", v "three", v "four", v "five"].map
      (applySubst capturedCaller) =
      [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
        encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient,
        encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)] := by
    simp [capturedCaller, applySubst, Subst.lookup]
  have variableCall := ScopedInstantiationExecution.reduct_ordinary_variables_returns_in_extension
    CollectionSelectionExecution.scopedLibrary.runtime scopedInstantiation_agreement
    capturedCaller state rule spec ambient assignment ["one", "two", "three", "four", "five"]
    capturedNames
  exact captured_call_returns CollectionSelectionExecution.scopedLibrary.runtime
    capturedCaller [] state state "gslt:rule:scope-reduct"
    [v "one", v "two", v "three", v "four", v "five"]
    [.symbol "None", encoded (InferenceCettaWire.AuthoredRule.rewriteTerm rule),
      encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm spec), number ambient,
      encoded (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment)] _
    (ordinary_dispatch _ 5 (by simp [operationArities])) (by decide)
    (raw_arguments _ 5 (by simp [operationArities]) _ rfl)
    (raw_arguments _ 5 (by simp [operationArities]) _ rfl)
    (by simpa [applySubst, Subst.lookup] using capturedNames) variableCall

@[metta_head "gslt:collection-machine:firing"]
theorem firing_returns (state : Effects.State) (request : Request) (receipt : Receipt) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:firing"
        [encoded (requestTerm request), encoded (receiptTerm receipt)])
      state (encoded (encodeOption firingTerm (firing? request receipt))) := by
  have reduced' := scoped_reduct_returns state request.rule request.spec request.ambient
    receipt.matching.assignment
  have selected := by
    metta_lift CollectionSelectionExecution.checked
      ["operation", "rule", "spec", "ambient", "assignment"] reduced'
  have available := by
    metta_lift ScopedCollectionExecution.checked
      ["operation", "rule", "spec", "ambient", "assignment"] selected
  cases made : ScopedRuleMatching.reduct? request.rule request.spec request.ambient
      receipt.matching.assignment <;>
    collection_machine_eval [available] unfolding [ScopedCollectionMachine.firing?, made,
      firingTerm, receiptTerm, requestTerm, encodeOption,
      RuleInstantiationExecution.GeneralExecution.matcherRequestTerm,
      ScopedCollectionMachine.Request.machine,
      MatchAutomataBindingExecution.patternOptionTerm,
      InferenceCettaWire.AuthoredRule.rewriteTerm,
      RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm,
      RuleInstantiationExecution.GeneralExecution.traceTerm]

@[metta_head "gslt:collection-machine:firings"]
theorem firings_returns (state : Effects.State) (request : Request) : ∀ receipts : List Receipt,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:firings"
        [encoded (requestTerm request), encoded (encodeList receiptTerm receipts)])
      state (encoded (encodeList firingTerm (receipts.filterMap (firing? request))))
  | [] => by
      collection_machine_eval unfolding [List.filterMap_nil]
  | receipt :: tail => by
      have first := firing_returns state request receipt
      have later := firings_returns state request tail
      cases made : firing? request receipt <;>
        collection_machine_eval [first, later] unfolding [List.filterMap_cons, made, encodeOption]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionFiringExecution
