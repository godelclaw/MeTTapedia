import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorScan
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.BridgeCoverage

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option maxErrors 8

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperations

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.BagNormalForm.WithAuthoredEquations.AlgebraFocus
open RecursiveView Retained RetainedWire
open Mettapedia.GSLT.LanguageDef.WellSorted
open InferenceCettaWire.AuthoredRule (typeTerm parameterTerm)
open InferenceCettaWire.ContextObservation (contextTerm)
open InferenceCettaWire (encodePattern)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file% "../../../../../../../../../metta/gslt/lib/gslt_collection_retained_operations.metta"
    sha256 "43bc5c8eabd5cab12cdfdf3b9ab599af4a4ef7653109f2db21bd8d8dab6d940c"

private def completeSource : SpaceSemantics.Program :=
  (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program

private def inherited : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[134]'(by decide +kernel),
    completeSource.equations[12]'(by decide +kernel),completeSource.equations[26]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[134]'(by decide +kernel),
    completeSource.declarations[12]'(by decide +kernel),completeSource.declarations[26]'(by decide +kernel)]

def library : Library :=
  ⟨{equations := [],declarations := []},inherited.append source.program,["gslt:"]⟩

def runtime : SpaceSemantics.Program := RetainedConstructors.runtime.append source.program

theorem checked : library.check = true := by decide +kernel

def proofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || (library.runtime.equations.map (·.head)).contains head

private def rowFields (row : SpaceSemantics.Equation) := (row.head,row.arguments,row.body)

private theorem rowFields_injective : Function.Injective rowFields := by
  intro first second same
  cases first
  cases second
  simpa only [rowFields,Prod.mk.injEq,SpaceSemantics.Equation.mk.injEq] using same

theorem runtime_agreement : ProgramAgreementOn proofHeads library.runtime runtime := by
  apply programAgreementOn_of_retained_rows
  · apply List.map_injective_iff.mpr rowFields_injective
    decide +kernel
  · decide +kernel

variable (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn proofHeads library.runtime program)

theorem nil_matches_encoded_list {α : Type} (element : α → Term)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst) (items : List α) :
    SpaceSemantics.matchValue bindings (.symbol "LNil") (encoded (encodeList element items)) =
      match items with
      | [] => some bindings
      | _ :: _ => none := by
  cases items <;> simp [SpaceSemantics.matchValue, encodeList, CettaWireAtom.encode,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom]

syntax "view_eval" " using " "(" term ")" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| view_eval using ($agreement) $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in checked using $agreement; metta_eval [$facts,*] with checked in $agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        encodeList, occurrenceTerm, spellingTerm, valueTerm, taskTerm, continuationTerm,
        expansionTerm, stateTerm, queryTerm, focusTerm, contextTerm, encodeOption, nil_matches_encoded_list, InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns,
        InferenceCettaWire.encodeList, InferenceCettaWire.encodePatterns_eq_encodeList,
        InferenceCettaWire.encodeBinder, InferenceCettaWire.encodeRest,
        InferenceCettaWire.encodeCollectionType, $extra,*]))

syntax "view_data" " using " "(" term ")" : tactic
macro_rules
  | `(tactic| view_data using ($agreement)) =>
    `(tactic| (apply data_in_program_returns $agreement _ _ _ _ (by decide +kernel) (by decide +kernel); simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?, Library.bind,
        encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        expand, expansionTerm, taskTerm, valueTerm, spellingTerm, continuationTerm, encodeList,
        InferenceCettaWire.encodePattern, InferenceCettaWire.encodePatterns_eq_encodeList,
        InferenceCettaWire.encodeList, InferenceCettaWire.encodeBinder,
        InferenceCettaWire.encodeRest, InferenceCettaWire.encodeCollectionType]; rfl))

include agreement in
@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (host : Effects.State) :
    ∀ (first second : List α),
    PureReturns program [] host
      (apply "gslt:automata:append" [encoded (encodeList element first), encoded (encodeList element second)])
      host (encoded (encodeList element (first ++ second)))
  | [], second => by view_eval using (agreement)
  | first :: later, second => by
      have rest := append_returns element host later second
      view_eval using (agreement) [rest]

include agreement in
@[metta_head "gslt:collection-presentation:view-values"]
theorem values_returns (host : Effects.State) : ∀ (occurrences : List SourceOccurrence),
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-values" [encoded (encodeList occurrenceTerm occurrences)])
      host (encoded (encodeList encodePattern (occurrences.map SourceOccurrence.value)))
  | [] => by view_eval using (agreement)
  | first :: later => by
      have rest := values_returns host later
      cases first
      view_eval using (agreement) [rest]

include agreement in
/-- Every return continuation realizes the actual retained producer transition;
the full parent frame and remaining continuation travel with the returned task. -/
@[metta_head "gslt:collection-presentation:view-return"]
theorem return_returns (host : Effects.State) (parameters : Parameters) {kind : Kind}
    (value : Value kind) (next : Continuation kind) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-return" [encoded (valueTerm value), encoded (continuationTerm next)])
      host (encoded (expansionTerm (expand parameters (.returned value next)))) := by
  cases next with
  | done =>
      cases value
      view_eval using (agreement) unfolding [expand]
  | application parent label next =>
      cases value
      view_eval using (agreement) unfolding [expand]
      view_data using (agreement)
  | collection parent residual next =>
      rcases value with ⟨targets, frames⟩
      have values := values_returns program agreement host residual
      have appended := append_returns program agreement encodePattern host targets (residual.map SourceOccurrence.value)
      view_eval using (agreement) [values, appended] unfolding [expand]
      view_data using (agreement)
  | lambda parent binder next =>
      cases value
      view_eval using (agreement) unfolding [expand]
      view_data using (agreement)
  | multiLambda parent arity binders next =>
      cases value
      view_eval using (agreement) unfolding [expand]
      view_data using (agreement)
  | tail query next =>
      cases value
      view_eval using (agreement) unfolding [expand]
  | prepend head next =>
      rcases value with ⟨targets, frames⟩
      rcases head with ⟨target, before⟩
      have appended := append_returns program agreement frameTerm host before frames
      view_eval using (agreement) [appended] unfolding [expand]

#print axioms checked
#print axioms append_returns
#print axioms values_returns
#print axioms return_returns

include agreement in
@[metta_head "gslt:complete:take"]
theorem take_returns {α : Type} (element : α → Term) (host : Effects.State)
    (count : Nat) (items : List α) :
    PureReturns program [] host
      (apply "gslt:complete:take" [number count, encoded (encodeList element items)])
      host (encoded (encodeList element (items.take count))) := by
  induction count generalizing items with
  | zero => view_eval using (agreement) unfolding [List.take]
  | succ count recurse =>
      cases items with
      | nil => view_eval using (agreement) unfolding [List.take]
      | cons first later =>
          have rest := recurse later
          view_eval using (agreement) [rest] unfolding [List.take]

include agreement in
@[metta_head "gslt:complete:drop"]
theorem drop_returns {α : Type} (element : α → Term) (host : Effects.State)
    (count : Nat) (items : List α) :
    PureReturns program [] host
      (apply "gslt:complete:drop" [number count, encoded (encodeList element items)])
      host (encoded (encodeList element (items.drop count))) := by
  induction count generalizing items with
  | zero => view_eval using (agreement) unfolding [List.drop]
  | succ count recurse =>
      cases items with
      | nil => view_eval using (agreement) unfolding [List.drop]
      | cons first later =>
          have rest := recurse later
          view_eval using (agreement) [rest] unfolding [List.drop]

include agreement in
@[metta_head "gslt:premise:parameter-type"]
theorem parameter_type_returns (host : Effects.State) (parameter : TermParam) :
    PureReturns program [] host
      (apply "gslt:premise:parameter-type" [encoded (parameterTerm parameter)])
      host (encoded (encodeOption typeTerm (parameterType? parameter))) := by
  cases parameter with
  | simple name type =>
      view_eval using (agreement) unfolding [parameterType?, parameterTerm, typeTerm]
  | abstractionNamed binder name type =>
      cases type <;>
        view_eval using (agreement) unfolding [parameterType?, parameterTerm, typeTerm]
  | multiAbstractionNamed binders name type =>
      cases type with
      | arrow domain codomain =>
          cases domain <;>
            view_eval using (agreement) unfolding [parameterType?, parameterTerm, typeTerm]
      | base sort =>
          view_eval using (agreement) unfolding [parameterType?, parameterTerm, typeTerm]
      | multiBinder body =>
          view_eval using (agreement) unfolding [parameterType?, parameterTerm, typeTerm]
      | collection kind body =>
          view_eval using (agreement) unfolding [parameterType?, parameterTerm, typeTerm]

include agreement in
@[metta_head "gslt:collection-presentation:view-context-comp"]
theorem context_comp_returns (host : Effects.State) (outer inner : OneHoleContext) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-context-comp"
        [encoded (contextTerm outer), encoded (contextTerm inner)])
      host (encoded (contextTerm (outer.comp inner))) := by
  induction outer with
  | hole => view_eval using (agreement) unfolding [OneHoleContext.comp]
  | apply label before context after recurse =>
      view_eval using (agreement) [recurse] unfolding [OneHoleContext.comp]
  | lambda binder context recurse =>
      view_eval using (agreement) [recurse] unfolding [OneHoleContext.comp]
  | multiLambda arity binders context recurse =>
      view_eval using (agreement) [recurse] unfolding [OneHoleContext.comp]
  | substBody context replacement recurse =>
      view_eval using (agreement) [recurse] unfolding [OneHoleContext.comp]
  | substReplacement body context recurse =>
      view_eval using (agreement) [recurse] unfolding [OneHoleContext.comp]
  | collection kind before context after rest recurse =>
      view_eval using (agreement) [recurse] unfolding [OneHoleContext.comp]

include agreement in
/-- Both child-query constructors realize one actual retained transition.
Remaining schemas, source parameters, bound contexts and zippers stay in the task. -/
@[metta_head "gslt:collection-presentation:view-children"]
theorem children_returns (host : Effects.State) (parameters : Parameters)
    (query : Query .children) (next : Continuation .children) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-children"
        [encoded (queryTerm query), encoded (continuationTerm next)])
      host (encoded (expansionTerm (expand parameters (.request query next)))) := by
  cases query with
  | arguments schemaBound path bound label outer originals index schemas sources arguments =>
      cases outer with
      | none =>
          cases schemas <;> cases sources <;> cases arguments <;>
            view_eval using (agreement) unfolding [expand]
      | some context =>
          cases schemas <;> cases sources <;> cases arguments
          all_goals try (solve | view_eval using (agreement) unfolding [expand])
          rename_i schema laterSchemas source laterSources parameter laterParameters
          have typed := parameter_type_returns program agreement host parameter
          cases found : parameterType? parameter with
          | none =>
              rw [found] at typed
              view_eval using (agreement) [typed] unfolding [expand, found]
          | some expected =>
              rw [found] at typed
              have taken := take_returns program agreement encodePattern host index originals
              have dropped := drop_returns program agreement encodePattern host (index + 1) originals
              have composed := context_comp_returns program agreement host context
                (.apply label (originals.take index) .hole (originals.drop (index + 1)))
              have extended := append_returns program agreement Term.natural host path [index]
              simp only [expand, found]
              view_eval using (agreement) [typed, taken, dropped, composed, extended]
                unfolding [expand, found]
  | groups schemaBound path bound index schemas groups =>
      cases schemas <;> cases groups
      all_goals try (solve | view_eval using (agreement) unfolding [expand])
      rename_i schema laterSchemas group laterGroups
      have extended := append_returns program agreement Term.natural host path [index]
      view_eval using (agreement) [extended] unfolding [expand]

#print axioms nil_matches_encoded_list
#print axioms take_returns
#print axioms drop_returns
#print axioms parameter_type_returns
#print axioms context_comp_returns
#print axioms children_returns


include agreement in
@[metta_head "gslt:collection-presentation:view-commit"]
theorem commit_returns (host : Effects.State) (pending children : List Task)
    (answers published : List Spelling) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-commit"
        [encoded (encodeList taskTerm pending), encoded (encodeList spellingTerm answers),
         encoded (expansionTerm (children,published))])
      host (encoded (stateTerm ⟨children ++ pending, answers ++ published⟩)) := by
  have agenda := append_returns program agreement taskTerm host children pending
  have account := append_returns program agreement spellingTerm host answers published
  view_eval using (agreement) [agenda,account]


include agreement in
@[metta_head "gslt:collection-presentation:view-complete"]
theorem complete_returns (host : Effects.State) (state : State) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-complete" [encoded (stateTerm state)])
      host (Effects.boolean (complete state)) := by
  rcases state with ⟨agenda,answers⟩
  cases agenda <;> view_eval using (agreement) unfolding [complete]

include agreement in
@[metta_head "gslt:collection-presentation:view-answers"]
theorem answers_returns (host : Effects.State) (state : State) :
    PureReturns program [] host
      (apply "gslt:collection-presentation:view-answers" [encoded (stateTerm state)])
      host (encoded (encodeList spellingTerm state.answers)) := by
  cases state
  view_eval using (agreement)



#print axioms runtime_agreement
#print axioms commit_returns
#print axioms complete_returns
#print axioms answers_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperations
