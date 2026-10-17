import Mettapedia.Languages.MeTTa.HE.ArgumentResultCorrectness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance

/-!
# Constructed sequential histories for the independent HE evaluator

A successful argument judgment determines a history of selected values and
their binding states. The history is extracted from the independent,
fuel-free evaluator rules, rather than supplied as a certificate about a
recursive implementation. Its inverse constructs the exact argument judgment.
Splitting a history retains its intermediate binding endpoint and the same
finite readout table for all pending operands.

These laws connect the semantic argument/return boundary. Native substitution,
binding merge, domain refinement and callback execution are separate services;
no theorem here identifies those services with CeTTa's implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval

/-- A branch's chosen arguments, exact binding endpoints, and remaining
syntax. A completed history has empty remaining argument and type lists. A
prefix retains those lists, so names in pending evaluations remain protected. -/
inductive HistoryRel (space : Space) (dispatch : Spec.Eval.GroundedDispatch) :
    List Atom → EvalTypeService →
    List Atom → List Atom → BindingFrame → List FrameResult → BindingFrame →
    (remainingArguments : List Atom := []) → (remainingTypes : List Atom := []) → Prop where
  | nil {live : List Atom} {typing : EvalTypeService} {arguments types : List Atom}
      (bindings : BindingFrame) :
      HistoryRel space dispatch live typing arguments types bindings [] bindings arguments types
  | selected {live : List Atom} {typing : EvalTypeService}
      {argument expected : Atom} {arguments types remainingArguments remainingTypes : List Atom}
      {incoming outgoing : BindingFrame} {head : FrameResult} {selected : List FrameResult} :
      EvalAtomRawRel space dispatch (arguments ++ types ++ live) (typing := typing)
        argument expected incoming head →
      (¬IsEmptyOrErrorRel head.1 ∨ head.1 = argument) →
      HistoryRel space dispatch (head.1 :: live) typing arguments types head.2 selected outgoing
        remainingArguments remainingTypes →
      HistoryRel space dispatch live typing (argument :: arguments) (expected :: types)
        incoming (head :: selected) outgoing remainingArguments remainingTypes

theorem history_lengths
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types remainingArguments remainingTypes : List Atom}
    {incoming outgoing : BindingFrame} {selected : List FrameResult}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing
      remainingArguments remainingTypes) :
    arguments.length = selected.length + remainingArguments.length ∧
      types.length = selected.length + remainingTypes.length := by
  induction history with
  | nil => simp
  | selected _ _ _ ih => simp only [List.length_cons]; omega

private theorem complete_history_to_arguments
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types remainingArguments remainingTypes : List Atom}
    {incoming outgoing : BindingFrame} {selected : List FrameResult}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing
      remainingArguments remainingTypes) :
    remainingArguments = [] → remainingTypes = [] →
    InterpretArgsRel space dispatch live (typing := typing) arguments types incoming
      (argumentPacket (selected.map Prod.fst), outgoing) := by
  induction history with
  | nil bindings =>
      intro argumentsDone typesDone
      subst argumentsDone typesDone
      exact .nil bindings
  | @selected live typing argument expected arguments types remainingArguments remainingTypes incoming outgoing head selected evaluated clean tail ih =>
      intro argumentsDone typesDone
      simpa only [List.map_cons, argumentValues_packet] using
        InterpretArgsRel.success argument arguments expected types incoming head
          (argumentPacket (selected.map Prod.fst), outgoing) evaluated clean
          (ih argumentsDone typesDone) ⟨_, rfl⟩

theorem history_to_arguments
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom}
    {incoming outgoing : BindingFrame} {selected : List FrameResult}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing) :
    InterpretArgsRel space dispatch live (typing := typing) arguments types incoming
      (argumentPacket (selected.map Prod.fst), outgoing) :=
  complete_history_to_arguments history rfl rfl

private theorem packet_is_not_failure (values : List Atom) :
    ¬IsEmptyOrErrorRel (argumentPacket values) := by
  rw [Spec.Type.Conformance.isEmptyOrErrorRel_iff_isEmptyOrError]
  simp

/-- Every successful independent argument derivation constructs the sequential
binding witness; no per-position provenance assumption is needed. -/
theorem arguments_to_history
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types values : List Atom}
    {incoming outgoing : BindingFrame}
    (derivation : InterpretArgsRel space dispatch live (typing := typing)
      arguments types incoming (argumentPacket values, outgoing)) :
    ∃ selected, HistoryRel space dispatch live typing arguments types incoming selected outgoing ∧
      selected.map Prod.fst = values := by
  induction arguments generalizing live types values incoming outgoing with
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
          | mk tailValue tailBindingFrame =>
              change tailValue = argumentPacket tailValues at tailPacket
              subst tailValue
              obtain ⟨selected, history, selectedValues⟩ := ih tailDerivation
              refine ⟨head :: selected, .selected evaluated clean history, ?_⟩
              simp only [List.map_cons, selectedValues, argumentValues_packet]

theorem arguments_history_iff
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types values : List Atom}
    {incoming outgoing : BindingFrame} :
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
inductive FailureHistoryRel (space : Space) (dispatch : Spec.Eval.GroundedDispatch) :
    List Atom → EvalTypeService →
    List Atom → List Atom → BindingFrame → List FrameResult → FrameResult → Prop where
  | failed {live : List Atom} {typing : EvalTypeService}
      {argument expected : Atom} {arguments types : List Atom}
      {incoming : BindingFrame} {failure : FrameResult} :
      EvalAtomRawRel space dispatch (arguments ++ types ++ live) (typing := typing)
        argument expected incoming failure →
      IsEmptyOrErrorRel failure.1 → failure.1 ≠ argument →
      FailureHistoryRel space dispatch live typing (argument :: arguments) (expected :: types)
        incoming [] failure
  | selected {live : List Atom} {typing : EvalTypeService}
      {argument expected : Atom} {arguments types : List Atom}
      {incoming : BindingFrame} {head failure : FrameResult} {selected : List FrameResult} :
      EvalAtomRawRel space dispatch (arguments ++ types ++ live) (typing := typing)
        argument expected incoming head →
      (¬IsEmptyOrErrorRel head.1 ∨ head.1 = argument) →
      FailureHistoryRel space dispatch (head.1 :: live) typing arguments types head.2 selected failure →
      FailureHistoryRel space dispatch live typing (argument :: arguments) (expected :: types)
        incoming (head :: selected) failure

theorem failure_history_is_failure
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : BindingFrame}
    {selected : List FrameResult} {failure : FrameResult}
    (history : FailureHistoryRel space dispatch live typing arguments types incoming selected failure) :
    IsEmptyOrErrorRel failure.1 := by
  induction history with
  | failed _ failed _ => exact failed
  | selected _ _ _ ih => exact ih

theorem failure_history_to_arguments
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : BindingFrame}
    {selected : List FrameResult} {failure : FrameResult}
    (history : FailureHistoryRel space dispatch live typing arguments types incoming selected failure) :
    InterpretArgsRel space dispatch live (typing := typing) arguments types incoming failure := by
  induction history with
  | @failed live typing argument expected arguments types incoming failure evaluated failed changed =>
      exact .headChangedError argument arguments expected types incoming failure evaluated failed changed
  | @selected live typing argument expected arguments types incoming head failure selected evaluated clean tail ih =>
      exact .tailError argument arguments expected types incoming head failure evaluated clean ih
        (fun values packet => packet_is_not_failure values
          (packet ▸ failure_history_is_failure tail))

theorem arguments_to_failure_history
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : BindingFrame}
    {failure : FrameResult}
    (derivation : InterpretArgsRel space dispatch live (typing := typing)
      arguments types incoming failure)
    (notPacket : ∀ values, failure.1 ≠ argumentPacket values) :
    ∃ selected, FailureHistoryRel space dispatch live typing arguments types incoming selected failure := by
  induction arguments generalizing live types incoming failure with
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
    {typing : EvalTypeService} {arguments types : List Atom} {incoming : BindingFrame}
    {failure : FrameResult} (notPacket : ∀ values, failure.1 ≠ argumentPacket values) :
    InterpretArgsRel space dispatch live (typing := typing) arguments types incoming failure ↔
      ∃ selected, FailureHistoryRel space dispatch live typing arguments types incoming selected failure := by
  constructor
  · intro derivation
    exact arguments_to_failure_history derivation notPacket
  · rintro ⟨selected, history⟩
    exact failure_history_to_arguments history

/-- Join a retained prefix to its remaining computation. The suffix begins
with every selected value still live; the prefix has protected the complete
pending syntax at each evaluation. -/
theorem history_append
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments nextArguments types nextTypes : List Atom}
    {incoming middle outgoing : BindingFrame} {first next : List FrameResult}
    (initialHistory : HistoryRel space dispatch live typing arguments types incoming first middle
      nextArguments nextTypes)
    (suffix : HistoryRel space dispatch ((first.map Prod.fst).reverse ++ live) typing
      nextArguments nextTypes middle next outgoing) :
    HistoryRel space dispatch live typing arguments types incoming (first ++ next) outgoing := by
  induction initialHistory generalizing outgoing next with
  | nil => simpa using suffix
  | selected evaluated clean _ ih =>
      apply HistoryRel.selected evaluated clean
      apply ih
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using suffix

private theorem complete_history_cut
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types remainingArguments remainingTypes : List Atom}
    {incoming outgoing : BindingFrame} {selected : List FrameResult}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing
      remainingArguments remainingTypes) :
    remainingArguments = [] → remainingTypes = [] → ∀ count,
    ∃ middle,
      HistoryRel space dispatch live typing arguments types
        incoming (selected.take count) middle (arguments.drop count) (types.drop count) ∧
      HistoryRel space dispatch (((selected.take count).map Prod.fst).reverse ++ live) typing
        (arguments.drop count) (types.drop count) middle (selected.drop count) outgoing := by
  induction history with
  | nil bindings =>
      intro argumentsDone typesDone count
      subst argumentsDone typesDone
      simpa using Exists.intro bindings (And.intro (HistoryRel.nil bindings) (HistoryRel.nil bindings))
  | selected evaluated clean tail ih =>
      intro argumentsDone typesDone count
      cases count with
      | zero =>
          subst argumentsDone typesDone
          exact ⟨_, .nil _, .selected evaluated clean tail⟩
      | succ count =>
          obtain ⟨middle, initialHistory, suffix⟩ := ih argumentsDone typesDone count
          refine ⟨middle, .selected evaluated clean initialHistory, ?_⟩
          simpa only [List.take_succ_cons, List.drop_succ_cons, List.map_cons,
            List.reverse_cons, List.append_assoc, List.singleton_append] using suffix

/-- The paused binding state is constructed by splitting the actual history.
The prefix retains its pending argument and type syntax, and the suffix keeps
all selected values live. Neither side silently erases freshness obligations. -/
theorem history_cut
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {arguments types : List Atom}
    {incoming outgoing : BindingFrame} {selected : List FrameResult}
    (history : HistoryRel space dispatch live typing arguments types incoming selected outgoing)
    (count : Nat) :
    ∃ middle,
      HistoryRel space dispatch live typing arguments types
        incoming (selected.take count) middle (arguments.drop count) (types.drop count) ∧
      HistoryRel space dispatch (((selected.take count).map Prod.fst).reverse ++ live) typing
        (arguments.drop count) (types.drop count) middle (selected.drop count) outgoing :=
  complete_history_cut history rfl rfl count

/-- Any finite nesting is raw syntax under Atom demand, including a nested
quotation, a binding form or an error-shaped datum. -/
theorem atom_demand_raw (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (value : Atom) (bindings : BindingFrame) :
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
    (live : List Atom) (typing : EvalTypeService) (values : List Atom) (bindings : BindingFrame) :
    HistoryRel space dispatch live typing values (List.replicate values.length Atom.atomType)
      bindings (values.map fun value => (value, bindings)) bindings := by
  induction values generalizing live with
  | nil => exact .nil _
  | cons value values ih =>
      exact .selected (atom_demand_raw space dispatch _ typing value bindings) (Or.inr rfl) (ih _)

/-- The chosen head, argument history and return demand construct a full
independent typed-application derivation. -/
theorem application_from_history
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {operator expected : Atom} {arguments rawTypes types : List Atom}
    {policy : SelectedTypePolicy} {incoming applicable outgoing : BindingFrame}
    {head : FrameResult} {selected : List FrameResult} {result : FrameResult}
    (operatorTypes : typing.typesOf space operator rawTypes)
    (instantiated : typing.instantiateTypes
      (invocationTypeScope [] live (.expression (operator :: arguments)) expected incoming) rawTypes types)
    (scanned : typing.candidateScan
      (invocationTypeScope [] live (.expression (operator :: arguments)) expected incoming)
      space (.expression (operator :: arguments)) expected incoming types (.success policy applicable))
    (renewed : BindingFrame.Update .renew incoming applicable)
    (headEvaluated : EvalAtomRawRel space dispatch
      (policy.functionType :: arguments ++
        (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType) :: live)
      (protectedScope := expectedApplicationScope (.expression (operator :: arguments)) expected)
      (typing := typing) operator policy.functionType applicable head)
    (headOrdinary : ¬IsEmptyOrErrorRel head.1)
    (argumentsEvaluated : HistoryRel space dispatch
      (head.1 ::
        (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType) :: live) typing
      arguments policy.argumentTypes head.2 selected outgoing)
    (returned : CallRel space dispatch live (typing := typing)
      (.expression (head.1 :: selected.map Prod.fst))
      (if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType)
      outgoing result) :
    InterpretExpressionRel space dispatch live (typing := typing)
      (.expression (operator :: arguments)) expected incoming result := by
  have interpreted : InterpretFunctionRel space dispatch
      ((if policy.returnType = Atom.expressionType then Atom.undefinedType else policy.returnType) :: live)
      (typing := typing)
      (.expression (operator :: arguments)) policy.functionType expected applicable
      (.expression (head.1 :: selected.map Prod.fst), outgoing) := by
    simpa only [argumentValues_packet] using
      InterpretFunctionRel.success _ _ _ _ policy.returnType _ _ _ head
        (argumentPacket (selected.map Prod.fst), outgoing) rfl policy.isFunction
        headEvaluated headOrdinary (history_to_arguments argumentsEvaluated) ⟨_, rfl⟩
  exact .functionPath _ _ _ arguments rawTypes types policy _ incoming applicable _ result rfl
    operatorTypes instantiated scanned renewed rfl interpreted returned

end Mettapedia.Languages.MeTTa.HE.RetainedArgumentSpecification
