import Mettapedia.Languages.MeTTa.HE.Correctness
import Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-!
# Argument-result invariants and raw-data preservation

Both HE argument judgments distinguish tagged lists from propagated failures.
Their result-form laws are derived from their rules. The executable evaluator
inherits its law through its proved soundness theorem. The raw-data theorem
covers arbitrary lists of atoms, bindings and finite nesting, at every
sufficient fuel value. It preserves list order and occurrences.

These are argument-protocol guarantees. They do not establish correspondence
of complete HE, PeTTa, Prime or native evaluator configurations.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem InterpretArgs.packet_or_error
    {space : Space} {dispatch : GroundedDispatch}
    {args types : List Atom} {bindings : Bindings} {result : ResultPair}
    (derivation : InterpretArgs space dispatch args types bindings result) :
    (∃ values, result.1 = argumentPacket values) ∨ isEmptyOrError result.1 = true := by
  induction args generalizing types bindings result with
  | nil =>
      cases derivation
      exact Or.inl ⟨[], rfl⟩
  | cons argument arguments ih =>
      cases derivation with
      | head_changed_error _ _ _ _ _ _ _ failed _ => exact Or.inr failed
      | cons_tail_error _ _ _ _ _ _ _ _ _ tail _ => exact ih tail
      | cons_ok _ _ _ _ _ _ _ _ _ _ _ => exact Or.inl ⟨_, rfl⟩

theorem Spec.Eval.InterpretArgsRel.packet_or_error
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : Spec.Eval.EvalTypeService}
    {args types : List Atom} {bindings : Bindings} {result : ResultPair}
    (derivation : Spec.Eval.InterpretArgsRel space dispatch live (typing := typing)
      args types bindings result) :
    (∃ values, result.1 = argumentPacket values) ∨ Spec.Eval.IsEmptyOrErrorRel result.1 := by
  induction args generalizing types bindings result with
  | nil =>
      cases derivation
      exact Or.inl ⟨[], rfl⟩
  | cons argument arguments ih =>
      cases derivation with
      | headChangedError _ _ _ _ _ _ _ failed _ => exact Or.inr failed
      | tailError _ _ _ _ _ _ _ _ _ tail _ => exact ih tail
      | success _ _ _ _ _ _ _ _ _ _ _ => exact Or.inl ⟨_, rfl⟩

theorem interpretArgs_packet_or_error
    {space : Space} {dispatch : GroundedDispatch} {args types : List Atom}
    {bindings : Bindings} {fuel : Nat} {result : ResultPair}
    (returned : result ∈ interpretArgs space dispatch args types bindings fuel) :
    (∃ values, result.1 = argumentPacket values) ∨ isEmptyOrError result.1 = true :=
  (interpretArgs_sound space dispatch args types bindings fuel result returned).packet_or_error

/-- A non-packet result of argument computation is an actual failure. -/
theorem interpretArgs_failure_is_error
    {space : Space} {dispatch : GroundedDispatch} {args types : List Atom}
    {bindings : Bindings} {fuel : Nat} {result : ResultPair}
    (returned : result ∈ interpretArgs space dispatch args types bindings fuel)
    (notSuccess : argumentsSucceeded result.1 = false) :
    isEmptyOrError result.1 = true := by
  rcases interpretArgs_packet_or_error returned with ⟨values, packet⟩ | failed
  · rw [packet, argumentsSucceeded_packet] at notSuccess
    cases notSuccess
  · exact failed

/-- Atom demand returns any input atom unchanged, including error-shaped data. -/
theorem evalAtom_raw_positive
    (space : Space) (dispatch : GroundedDispatch) (atom : Atom)
    (bindings : Bindings) (fuel : Nat) :
    evalAtom space dispatch atom Atom.atomType bindings (fuel + 1) =
      [(atom, bindings)] := by
  by_cases failed : isEmptyOrError atom = true
  · simp [evalAtom, failed]
  · have clean : isEmptyOrError atom = false := by
      cases checked : isEmptyOrError atom <;> simp_all
    simp [evalAtom, clean]

/-- Every raw argument list survives intact, with its exact order and multiplicity. -/
theorem interpretArgs_raw
    (space : Space) (dispatch : GroundedDispatch) (args : List Atom)
    (bindings : Bindings) (fuel : Nat) (enough : args.length < fuel) :
    interpretArgs space dispatch args (List.replicate args.length Atom.atomType)
      bindings fuel = [(argumentPacket args, bindings)] := by
  induction args generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp at enough
      | succ fuel => rfl
  | cons argument arguments ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          cases fuel with
          | zero => simp at enough
          | succ fuel =>
              have tailEnough : arguments.length < fuel + 1 := by
                simp only [List.length_cons] at enough
                omega
              change interpretArgs space dispatch (argument :: arguments)
                (Atom.atomType :: List.replicate arguments.length Atom.atomType)
                bindings (fuel + 1 + 1) = _
              rw [interpretArgs]
              simp only [evalAtom_raw_positive, List.flatMap_cons, List.flatMap_nil,
                bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
                if_false]
              rw [ih (fuel + 1) tailEnough]
              simp only [List.map_cons, List.map_nil,
                argumentsSucceeded_packet, Bool.true_eq_false, argumentValues_packet,
                List.append_nil, if_false]

/-- Arbitrary raw data in a successful packet cannot be mistaken for failure. -/
theorem interpretArgs_raw_not_failed
    (space : Space) (dispatch : GroundedDispatch) (args : List Atom)
    (bindings : Bindings) (fuel : Nat) (enough : args.length < fuel) :
    ∀ result ∈ interpretArgs space dispatch args
      (List.replicate args.length Atom.atomType) bindings fuel,
      argumentsSucceeded result.1 = true := by
  rw [interpretArgs_raw space dispatch args bindings fuel enough]
  intro result returned
  simp only [List.mem_cons, List.not_mem_nil, or_false] at returned
  subst result
  simp

end Mettapedia.Languages.MeTTa.HE
