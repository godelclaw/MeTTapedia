import Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution
import Mettapedia.Languages.MeTTa.HE.NativeArgumentControlMachine

/-!
# Constructed source replies at the independent HE boundary

Type lookup and raw evaluation use the actual existing source functions.
Their replies are proved against the independent type/evaluator judgments,
including the complete result list rather than just answer support. The
separate applicability component retains raw type-checking path multiplicity.

The source applicability and matching helpers are fuel-indexed. General
correspondence for non-raw applicability and casting remains separate from
these replies, as do native binding substitution and domain refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Type

theorem getAtomTypes_nonempty (space : Space) (value : Atom) :
    getAtomTypes space value ≠ [] := by
  have guard : ∀ types : List Atom,
      (if types.isEmpty then [Atom.undefinedType] else types) ≠ [] := by
    intro types
    cases types <;> simp
  exact guard _

/-- The whole source-ordered type list has an independent lookup derivation.
No theorem about a merely selected member is used as its substitute. -/
theorem source_types (space : Space) (value : Atom) :
    TypesOfRel space value (getAtomTypes space value) := by
  obtain ⟨type, member⟩ := List.exists_mem_of_ne_nil (getAtomTypes space value)
    (getAtomTypes_nonempty space value)
  obtain ⟨types, related, _⟩ :=
    (Conformance.typeOfRel_iff_mem_getAtomTypes space value type).mpr member
  rw [Conformance.typesOfRel_eq_getAtomTypes related]
  exact related

theorem source_types_iff (space : Space) (value : Atom) (types : List Atom) :
    getAtomTypes space value = types ↔ TypesOfRel space value types := by
  constructor
  · rintro rfl
    exact source_types space value
  · exact Conformance.typesOfRel_eq_getAtomTypes

/-- Atom demand has exactly one semantic result for arbitrary syntax,
bindings, nesting, quotation and error-shaped data. -/
theorem raw_result_unique
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {value : Atom} {bindings : BindingFrame} {result : FrameResult}
    (evaluated : EvalAtomRawRel space dispatch live (typing := typing)
      value Atom.atomType bindings result) : result = (value, bindings) := by
  cases evaluated with
  | emptyOrError => rfl
  | typePass => rfl
  | cast _ _ _ _ _ _ _ doesNotPass _ _ => exact (doesNotPass (Or.inl rfl)).elim
  | interpretSuccess _ _ _ _ _ _ _ doesNotPass _ _ _ => exact (doesNotPass (Or.inl rfl)).elim
  | interpretError _ _ _ _ _ _ _ doesNotPass _ _ _ => exact (doesNotPass (Or.inl rfl)).elim

theorem source_raw_reply_iff
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (value : Atom) (bindings : Bindings)
    (fuel : Nat) (result : ResultPair) :
    result ∈ evalAtom space source value Atom.atomType bindings (fuel + 1) ↔
      EvalAtomRawRel space semantic live (typing := typing)
        value Atom.atomType bindings result := by
  rw [evalAtom_raw_positive]
  simp only [List.mem_singleton]
  constructor
  · rintro rfl
    exact RetainedArgumentSpecification.atom_demand_raw space semantic live typing value bindings
  · intro evaluated
    exact BindingFrame.historicalResult_injective (raw_result_unique evaluated)

/-- Concrete source output constructs every reply witness in occurrence
order; the complete reply is a singleton rather than a support quotient. -/
theorem source_raw_reply
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (value : Atom) (bindings : Bindings)
    (fuel : Nat) :
    evalAtom space source value Atom.atomType bindings (fuel + 1) = [(value, bindings)] ∧
      EvalAtomRawRel space semantic live (typing := typing)
        value Atom.atomType bindings (value, bindings) :=
  ⟨evalAtom_raw_positive space source value bindings fuel,
    RetainedArgumentSpecification.atom_demand_raw space semantic live typing value bindings⟩

theorem raw_arguments_unique
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {values : List Atom} {bindings : BindingFrame} {result : FrameResult}
    (evaluated : InterpretArgsRel space dispatch live (typing := typing)
      values (List.replicate values.length Atom.atomType) bindings result) :
    result = (argumentPacket values, bindings) := by
  induction values generalizing live bindings result with
  | nil => cases evaluated; rfl
  | cons value values ih =>
      cases evaluated with
      | headChangedError _ _ _ _ _ head evaluated _ changed =>
          have returned := raw_result_unique evaluated
          cases returned
          exact (changed rfl).elim
      | tailError _ _ _ _ _ head tail evaluated _ remaining notPacket =>
          have returned := raw_result_unique evaluated
          cases returned
          have tailReturned := ih remaining
          cases tailReturned
          exact (notPacket values rfl).elim
      | success _ _ _ _ _ head tail evaluated _ remaining _ =>
          have returned := raw_result_unique evaluated
          cases returned
          have tailReturned := ih remaining
          cases tailReturned
          simp only [argumentValues_packet]

theorem source_raw_arguments_iff
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (values : List Atom) (bindings : Bindings)
    (fuel : Nat) (enough : values.length < fuel) (result : ResultPair) :
    result ∈ interpretArgs space source values (List.replicate values.length Atom.atomType)
      bindings fuel ↔
      InterpretArgsRel space semantic live (typing := typing)
        values (List.replicate values.length Atom.atomType) bindings result := by
  rw [interpretArgs_raw space source values bindings fuel enough]
  simp only [List.mem_singleton]
  constructor
  · rintro rfl
    simpa only [List.map_map, Function.comp_def, List.map_id', BindingFrame.historicalResult_pair] using
      RetainedArgumentSpecification.history_to_arguments
        (RetainedArgumentSpecification.raw_history space semantic live typing values bindings)
  · intro evaluated
    exact BindingFrame.historicalResult_injective (raw_arguments_unique evaluated)

/-- One raw source callback is delivered to its exact currently pending
endpoint. Semantic truth is constructed separately from serial acceptance. -/
theorem deliver_source_raw
    (configuration : NativeArgumentControl.Configuration) (argument : TypedApplyState)
    (prepared : NativeArgumentControl.Prepared) (rest : List NativeArgumentControl.Frame)
    (ticket : Nat) (pending : configuration.frames =
      .waiting (.evaluate argument prepared) ticket :: rest)
    (space : Space) (source : HE.GroundedDispatch) (semantic : Spec.Eval.GroundedDispatch)
    (live : List Atom) (typing : EvalTypeService) (fuel charge : Nat)
    (raw : prepared.domain = Atom.atomType) :
    ∃ after, NativeArgumentControl.DeliveryRel configuration
      ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
        .evaluated (evalAtom space source prepared.bound prepared.domain argument.env (fuel + 1)),
        charge⟩ after ∧
      EvalAtomRawRel space semantic live (typing := typing)
        prepared.bound prepared.domain argument.env (prepared.bound, argument.env) := by
  rw [raw, evalAtom_raw_positive]
  refine ⟨NativeArgumentControl.replied configuration rest
    ⟨(NativeArgumentControl.request configuration (.evaluate argument prepared) ticket).endpoint,
      .evaluated [(prepared.bound, argument.env)], charge⟩
    [.iterate (NativeArgumentControl.selectedSnapshot argument prepared
      [(prepared.bound, argument.env)]) prepared], ?_, ?_⟩
  · apply (NativeArgumentControl.deliver_iff _ _ _).mp
    exact NativeArgumentControl.evaluated_reply configuration argument prepared ticket rest
      [(prepared.bound, argument.env)] charge pending
  · exact RetainedArgumentSpecification.atom_demand_raw space semantic live typing
      prepared.bound argument.env

end Mettapedia.Languages.MeTTa.HE.FirstSuccessSourceReplies
