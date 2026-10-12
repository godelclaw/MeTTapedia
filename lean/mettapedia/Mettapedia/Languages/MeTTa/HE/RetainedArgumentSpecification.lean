import Mettapedia.Languages.MeTTa.HE.ArgumentResultCorrectness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance

/-!
# Constructed sequential histories for the independent HE evaluator

A successful argument judgment determines a history of selected values and
their binding states. The history is extracted from the independent,
fuel-free evaluator rules, rather than supplied as a certificate about a
recursive implementation. Its inverse constructs the exact argument judgment.
Splitting a history retains its intermediate binding endpoint.

These laws connect the semantic argument/return boundary. Native substitution,
binding merge, domain refinement and callback execution are separate services;
no theorem here identifies those services with CeTTa's implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval

/-- A branch's chosen arguments, with the exact binding endpoint between each
evaluation and the next. Error-shaped source data may be retained unchanged. -/
inductive HistoryRel (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) :
    List Atom → List Atom → Bindings → List ResultPair → Bindings → Prop where
  | nil (bindings : Bindings) :
      HistoryRel space dispatch live typing [] [] bindings [] bindings
  | selected {argument expected : Atom} {arguments types : List Atom}
      {incoming outgoing : Bindings} {head : ResultPair} {selected : List ResultPair} :
      EvalAtomRawRel space dispatch live (typing := typing)
        argument expected incoming head →
      (¬IsEmptyOrErrorRel head.1 ∨ head.1 = argument) →
      HistoryRel space dispatch live typing arguments types head.2 selected outgoing →
      HistoryRel space dispatch live typing (argument :: arguments) (expected :: types)
        incoming (head :: selected) outgoing

theorem history_lengths
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom}
    {incoming outgoing : Bindings} {selected : List ResultPair}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing) :
    arguments.length = selected.length ∧ types.length = selected.length := by
  induction history with
  | nil => exact ⟨rfl, rfl⟩
  | selected _ _ _ ih => simp [ih.1, ih.2]

theorem history_to_arguments
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom}
    {incoming outgoing : Bindings} {selected : List ResultPair}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing) :
    InterpretArgsRel space dispatch live (typing := typing) arguments types incoming
      (argumentPacket (selected.map Prod.fst), outgoing) := by
  induction history with
  | nil bindings => exact .nil bindings
  | @selected argument expected arguments types incoming outgoing head selected evaluated clean tail ih =>
      simpa only [List.map_cons, argumentValues_packet] using
        InterpretArgsRel.success argument arguments expected types incoming head
          (argumentPacket (selected.map Prod.fst), outgoing) evaluated clean ih ⟨_, rfl⟩

private theorem packet_is_not_failure (values : List Atom) :
    ¬IsEmptyOrErrorRel (argumentPacket values) := by
  rw [Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
  simp

/-- Every successful independent argument derivation constructs the sequential
binding witness; no per-position provenance assumption is needed. -/
theorem arguments_to_history
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types values : List Atom}
    {incoming outgoing : Bindings}
    (derivation : InterpretArgsRel space dispatch live (typing := typing)
      arguments types incoming (argumentPacket values, outgoing)) :
    ∃ selected, HistoryRel space dispatch live typing arguments types incoming selected outgoing ∧
      selected.map Prod.fst = values := by
  induction arguments generalizing types values incoming outgoing with
  | nil =>
      cases derivation
      exact ⟨[], .nil _, rfl⟩
  | cons argument arguments ih =>
      cases derivation with
      | headChangedError _ _ _ _ _ _ _ failed _ =>
          exact (packet_is_not_failure values failed).elim
      | tailError _ _ _ _ _ _ _ _ _ tail notPacket =>
          exact (notPacket values rfl).elim
      | success _ _ expected types incoming head tail evaluated clean tailDerivation packet =>
          obtain ⟨tailValues, tailPacket⟩ := packet
          cases tail with
          | mk tailValue tailBindings =>
              change tailValue = argumentPacket tailValues at tailPacket
              subst tailValue
              obtain ⟨selected, history, selectedValues⟩ := ih tailDerivation
              refine ⟨head :: selected, .selected evaluated clean history, ?_⟩
              simp only [List.map_cons, selectedValues, argumentValues_packet]

theorem arguments_history_iff
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types values : List Atom}
    {incoming outgoing : Bindings} :
    InterpretArgsRel space dispatch live (typing := typing)
      arguments types incoming (argumentPacket values, outgoing) ↔
    ∃ selected, HistoryRel space dispatch live typing arguments types incoming selected outgoing ∧
      selected.map Prod.fst = values := by
  constructor
  · exact arguments_to_history
  · rintro ⟨selected, history, rfl⟩
    exact history_to_arguments history

/-- A failing argument ends the selected prefix. Later arguments have not
been interpreted and acquire no invented binding endpoint. -/
inductive FailureHistoryRel (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) :
    List Atom → List Atom → Bindings → List ResultPair → ResultPair → Prop where
  | failed {argument expected : Atom} {arguments types : List Atom}
      {incoming : Bindings} {failure : ResultPair} :
      EvalAtomRawRel space dispatch live (typing := typing) argument expected incoming failure →
      IsEmptyOrErrorRel failure.1 → failure.1 ≠ argument →
      FailureHistoryRel space dispatch live typing (argument :: arguments) (expected :: types)
        incoming [] failure
  | selected {argument expected : Atom} {arguments types : List Atom}
      {incoming : Bindings} {head failure : ResultPair} {selected : List ResultPair} :
      EvalAtomRawRel space dispatch live (typing := typing) argument expected incoming head →
      (¬IsEmptyOrErrorRel head.1 ∨ head.1 = argument) →
      FailureHistoryRel space dispatch live typing arguments types head.2 selected failure →
      FailureHistoryRel space dispatch live typing (argument :: arguments) (expected :: types)
        incoming (head :: selected) failure

theorem failure_history_is_failure
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : Bindings}
    {selected : List ResultPair} {failure : ResultPair}
    (history : FailureHistoryRel space dispatch live typing arguments types incoming selected failure) :
    IsEmptyOrErrorRel failure.1 := by
  induction history with
  | failed _ failed _ => exact failed
  | selected _ _ _ ih => exact ih

theorem failure_history_to_arguments
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : Bindings}
    {selected : List ResultPair} {failure : ResultPair}
    (history : FailureHistoryRel space dispatch live typing arguments types incoming selected failure) :
    InterpretArgsRel space dispatch live (typing := typing) arguments types incoming failure := by
  induction history with
  | @failed argument expected arguments types incoming failure evaluated failed changed =>
      exact .headChangedError argument arguments expected types incoming failure evaluated failed changed
  | @selected argument expected arguments types incoming head failure selected evaluated clean tail ih =>
      exact .tailError argument arguments expected types incoming head failure evaluated clean ih
        (fun values packet => packet_is_not_failure values
          (packet ▸ failure_history_is_failure tail))

theorem arguments_to_failure_history
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : Bindings}
    {failure : ResultPair}
    (derivation : InterpretArgsRel space dispatch live (typing := typing)
      arguments types incoming failure)
    (notPacket : ∀ values, failure.1 ≠ argumentPacket values) :
    ∃ selected, FailureHistoryRel space dispatch live typing arguments types incoming selected failure := by
  induction arguments generalizing types incoming failure with
  | nil =>
      cases derivation
      exact (notPacket [] rfl).elim
  | cons argument arguments ih =>
      cases derivation with
      | headChangedError _ _ _ _ _ _ evaluated failed changed =>
          exact ⟨[], .failed evaluated failed changed⟩
      | tailError _ _ _ _ _ head failure evaluated clean tail failureNotPacket =>
          obtain ⟨selected, history⟩ := ih tail failureNotPacket
          exact ⟨head :: selected, .selected evaluated clean history⟩
      | success _ _ _ _ _ head tail _ _ _ _ =>
          exact (notPacket (head.1 :: argumentValues tail.1) rfl).elim

theorem arguments_failure_history_iff
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : Bindings}
    {failure : ResultPair} (notPacket : ∀ values, failure.1 ≠ argumentPacket values) :
    InterpretArgsRel space dispatch live (typing := typing) arguments types incoming failure ↔
      ∃ selected, FailureHistoryRel space dispatch live typing arguments types incoming selected failure := by
  constructor
  · intro derivation
    exact arguments_to_failure_history derivation notPacket
  · rintro ⟨selected, history⟩
    exact failure_history_to_arguments history

theorem history_append
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {firstArguments nextArguments firstTypes nextTypes : List Atom}
    {incoming middle outgoing : Bindings} {first next : List ResultPair}
    (initialHistory : HistoryRel space dispatch live typing firstArguments firstTypes incoming first middle)
    (suffix : HistoryRel space dispatch live typing nextArguments nextTypes middle next outgoing) :
    HistoryRel space dispatch live typing (firstArguments ++ nextArguments)
      (firstTypes ++ nextTypes) incoming (first ++ next) outgoing := by
  induction initialHistory with
  | nil => exact suffix
  | selected evaluated clean _ ih => exact .selected evaluated clean (ih suffix)

/-- The paused binding state is constructed by splitting the actual history. -/
theorem history_cut
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom}
    {incoming outgoing : Bindings} {selected : List ResultPair}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing)
    (count : Nat) :
    ∃ middle,
      HistoryRel space dispatch live typing (arguments.take count) (types.take count)
        incoming (selected.take count) middle ∧
      HistoryRel space dispatch live typing (arguments.drop count) (types.drop count)
        middle (selected.drop count) outgoing := by
  induction history generalizing count with
  | nil bindings => simpa using Exists.intro bindings (And.intro (HistoryRel.nil bindings) (HistoryRel.nil bindings))
  | @selected argument expected arguments types incoming outgoing head selected evaluated clean tail ih =>
      cases count with
      | zero => exact ⟨incoming, .nil _, .selected evaluated clean tail⟩
      | succ count =>
          obtain ⟨middle, initialHistory, suffix⟩ := ih count
          exact ⟨middle, .selected evaluated clean initialHistory, suffix⟩

/-- Any finite nesting is raw syntax under Atom demand, including a nested
quotation, a binding form or an error-shaped datum. -/
theorem atom_demand_raw (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (value : Atom) (bindings : Bindings) :
    EvalAtomRawRel space dispatch live (typing := typing)
      value Atom.atomType bindings (value, bindings) := by
  by_cases failed : IsEmptyOrErrorRel value
  · exact .emptyOrError value Atom.atomType bindings failed
  · cases value with
    | symbol name => exact .typePass _ _ Atom.symbolType _ failed (.symbol name) (Or.inl rfl)
    | var name => exact .typePass _ _ Atom.variableType _ failed (.variable name) (Or.inl rfl)
    | grounded value => exact .typePass _ _ Atom.groundedType _ failed (.grounded value) (Or.inl rfl)
    | expression values => exact .typePass _ _ Atom.expressionType _ failed (.expression values) (Or.inl rfl)

theorem raw_history (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (values : List Atom) (bindings : Bindings) :
    HistoryRel space dispatch live typing values (List.replicate values.length Atom.atomType)
      bindings (values.map fun value => (value, bindings)) bindings := by
  induction values with
  | nil => exact .nil _
  | cons value values ih =>
      exact .selected (atom_demand_raw space dispatch live typing value bindings) (Or.inr rfl) ih

/-- The chosen head, argument history and return demand construct a full
independent typed-application derivation. -/
theorem application_from_history
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {operator expected : Atom} {arguments types : List Atom}
    {policy : SelectedTypePolicy} {incoming applicable outgoing : Bindings}
    {head : ResultPair} {selected : List ResultPair} {result : ResultPair}
    (operatorTypes : typing.typesOf space operator types)
    (scanned : typing.candidateScan space (.expression (operator :: arguments)) expected
      incoming types (.success policy applicable))
    (headEvaluated : EvalAtomRawRel space dispatch live
      (protectedScope := expectedApplicationScope (.expression (operator :: arguments)) expected)
      (typing := typing) operator policy.functionType applicable head)
    (headOrdinary : ¬IsEmptyOrErrorRel head.1)
    (argumentsEvaluated : HistoryRel space dispatch live typing
      arguments policy.argumentTypes head.2 selected outgoing)
    (returned : CallRel space dispatch live (typing := typing)
      (.expression (head.1 :: selected.map Prod.fst))
      (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType)
      outgoing result) :
    InterpretExpressionRel space dispatch live (typing := typing)
      (.expression (operator :: arguments)) expected incoming result := by
  have interpreted : InterpretFunctionRel space dispatch live (typing := typing)
      (.expression (operator :: arguments)) policy.functionType expected applicable
      (.expression (head.1 :: selected.map Prod.fst), outgoing) := by
    simpa only [argumentValues_packet] using
      InterpretFunctionRel.success _ _ _ _ policy.returnType _ _ _ head
        (argumentPacket (selected.map Prod.fst), outgoing) rfl policy.isFunction
        headEvaluated headOrdinary (history_to_arguments argumentsEvaluated) ⟨_, rfl⟩
  exact .functionPath _ _ _ arguments types policy _ incoming applicable _ result rfl
    operatorTypes scanned rfl interpreted returned

end Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification
