import Mettapedia.Languages.MeTTa.HE.TypedApplyMachine

/-!
# Derivations of ordinary typed argument application

The direct evaluator and stack machine already retain an ordered frontier.
This judgment records the branch that licenses a result, including its exact
binding merges and binder extensions. A failed merge or extension licenses
no result. Selected argument values are retained in the recursive premise;
subsequent uses do not invoke the argument service again.

The leaf services are the explicit boundary of this component. Their native
implementation, recursive evaluator control, and dialect-specific policy
selection are separate obligations. In particular this judgment is not an
unrestricted identification with the published `InterpretArgs` judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.TypedApplyDerivation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The existing application's leaf operations, without correctness fields. -/
structure Services where
  evaluate : Atom → Atom → Bindings → ResultList
  apply : Bindings → Atom → Atom
  merge : Bindings → Bindings → Option Bindings
  extend : Bindings → Atom → Atom → Option Bindings
  raw : Atom → Bool

/-- An independently assembled argument branch. The selected value and its
resulting environment determine the entire remaining branch. -/
inductive Derivation (services : Services) : TypedApplyState → ResultPair → Prop where
  | complete (state : TypedApplyState)
      (done : state.idx ≥ state.origArgs.length) :
      Derivation services state
        (.expression (state.headAtom :: state.evArgs), state.env)
  | held (state : TypedApplyState) (live : state.idx < state.origArgs.length)
      (environment : Bindings) (result : ResultPair)
      (held : services.raw (getArgType state) = true ∨
        state.origArgs[state.idx].isVariable = true)
      (extended : services.extend state.env (getArgType state)
        (services.apply state.env state.origArgs[state.idx]) = some environment)
      (remaining : Derivation services
        (state.advance (services.apply state.env state.origArgs[state.idx]) environment)
        result) :
      Derivation services state result
  | changedError (state : TypedApplyState) (live : state.idx < state.origArgs.length)
      (value : Atom) (evaluated merged : Bindings)
      (interpreted : ¬(services.raw (getArgType state) = true ∨
        state.origArgs[state.idx].isVariable = true))
      (selected : (value, evaluated) ∈ services.evaluate
        (services.apply state.env state.origArgs[state.idx]) (getArgType state) state.env)
      (mergedBindings : services.merge state.env evaluated = some merged)
      (error : isEmptyOrError value = true)
      (changed : value ≠ state.origArgs[state.idx]) :
      Derivation services state (value, merged)
  | selected (state : TypedApplyState) (live : state.idx < state.origArgs.length)
      (value : Atom) (evaluated merged extended : Bindings) (result : ResultPair)
      (interpreted : ¬(services.raw (getArgType state) = true ∨
        state.origArgs[state.idx].isVariable = true))
      (selected : (value, evaluated) ∈ services.evaluate
        (services.apply state.env state.origArgs[state.idx]) (getArgType state) state.env)
      (mergedBindings : services.merge state.env evaluated = some merged)
      (ordinary : isEmptyOrError value = false ∨ value = state.origArgs[state.idx])
      (extendedBindings : services.extend merged (getArgType state) value = some extended)
      (remaining : Derivation services (state.advance value extended) result) :
      Derivation services state result

/-- Each direct result constructs a complete branch witness. -/
theorem direct_sound (services : Services) (state : TypedApplyState) (result : ResultPair)
    (member : result ∈ typedApplyDirect services.evaluate services.apply services.merge
      services.extend services.raw state) :
    Derivation services state result := by
  by_cases done : state.idx ≥ state.origArgs.length
  · have equal : result = (.expression (state.headAtom :: state.evArgs), state.env) := by
      simpa [base_case _ _ _ _ _ state done] using member
    subst result
    exact .complete state done
  · have live : state.idx < state.origArgs.length := by omega
    have unfolded := member
    unfold typedApplyDirect at unfolded
    simp only [done, dite_false] at unfolded
    change result ∈ (if services.raw (getArgType state) || state.origArgs[state.idx].isVariable
      then match services.extend state.env (getArgType state)
          (services.apply state.env state.origArgs[state.idx]) with
        | none => []
        | some environment => typedApplyDirect services.evaluate services.apply services.merge
            services.extend services.raw
            (state.advance (services.apply state.env state.origArgs[state.idx]) environment)
      else (services.evaluate (services.apply state.env state.origArgs[state.idx])
        (getArgType state) state.env).flatMap fun (value, evaluated) =>
        match services.merge state.env evaluated with
        | none => []
        | some merged =>
            if isEmptyOrError value && decide (value ≠ state.origArgs[state.idx])
            then [(value, merged)]
            else match services.extend merged (getArgType state) value with
              | none => []
              | some extended => typedApplyDirect services.evaluate services.apply services.merge
                  services.extend services.raw (state.advance value extended)) at unfolded
    by_cases held : services.raw (getArgType state) = true ∨
        state.origArgs[state.idx].isVariable = true
    · simp only [Bool.or_eq_true, if_pos held] at unfolded
      cases extended : services.extend state.env (getArgType state)
          (services.apply state.env state.origArgs[state.idx]) with
      | none => simp [extended] at unfolded
      | some environment =>
          rw [extended] at unfolded
          exact .held state live environment result held extended
            (direct_sound services _ result unfolded)
    · simp only [Bool.or_eq_true, if_neg held, List.mem_flatMap] at unfolded
      obtain ⟨⟨value, evaluated⟩, selected, remaining⟩ := unfolded
      cases mergedBindings : services.merge state.env evaluated with
      | none => simp [mergedBindings] at remaining
      | some merged =>
          rw [mergedBindings] at remaining
          by_cases error : isEmptyOrError value = true ∧ value ≠ state.origArgs[state.idx]
          · simp only [Bool.and_eq_true, decide_eq_true_eq, if_pos error,
              List.mem_singleton] at remaining
            subst result
            exact .changedError state live value evaluated merged held selected
              mergedBindings error.1 error.2
          · simp only [Bool.and_eq_true, decide_eq_true_eq, if_neg error] at remaining
            have ordinary : isEmptyOrError value = false ∨ value = state.origArgs[state.idx] := by
              by_cases failed : isEmptyOrError value = true
              · exact Or.inr (by by_contra changed; exact error ⟨failed, changed⟩)
              · exact Or.inl (Bool.eq_false_iff.mpr failed)
            cases extendedBindings : services.extend merged (getArgType state) value with
            | none => simp [extendedBindings] at remaining
            | some extended =>
                rw [extendedBindings] at remaining
                exact .selected state live value evaluated merged extended result held selected
                  mergedBindings ordinary extendedBindings
                  (direct_sound services _ result remaining)
termination_by state.origArgs.length - state.idx
decreasing_by all_goals simp only [TypedApplyState.advance]; omega

/-- A declared branch is realized by the independently recursive evaluator. -/
theorem direct_complete (services : Services) {state : TypedApplyState} {result : ResultPair}
    (derivation : Derivation services state result) :
    result ∈ typedApplyDirect services.evaluate services.apply services.merge
      services.extend services.raw state := by
  induction derivation with
  | complete state done => simp [base_case _ _ _ _ _ state done]
  | held state live environment result held extended remaining ih =>
      simp only [getArgType] at extended
      unfold typedApplyDirect
      simp only [show ¬state.idx ≥ state.origArgs.length by omega, dite_false]
      change result ∈ (if services.raw (getArgType state) || state.origArgs[state.idx].isVariable
        then _ else _)
      simp only [Bool.or_eq_true, if_pos held, extended]
      exact ih
  | changedError state live value evaluated merged interpreted selected mergedBindings error changed =>
      unfold typedApplyDirect
      simp only [show ¬state.idx ≥ state.origArgs.length by omega, dite_false]
      change (value, merged) ∈ (if services.raw (getArgType state) ||
        state.origArgs[state.idx].isVariable then _ else _)
      simp only [Bool.or_eq_true, if_neg interpreted, List.mem_flatMap]
      refine ⟨(value, evaluated), selected, ?_⟩
      simp [mergedBindings, error, changed]
  | selected state live value evaluated merged extended result interpreted selected
      mergedBindings ordinary extendedBindings remaining ih =>
      simp only [getArgType] at extendedBindings
      unfold typedApplyDirect
      simp only [show ¬state.idx ≥ state.origArgs.length by omega, dite_false]
      change result ∈ (if services.raw (getArgType state) ||
        state.origArgs[state.idx].isVariable then _ else _)
      simp only [Bool.or_eq_true, if_neg interpreted, List.mem_flatMap]
      refine ⟨(value, evaluated), selected, ?_⟩
      rcases ordinary with ordinary | ordinary
      · simpa [mergedBindings, ordinary, extendedBindings, TypedApplyState.advance] using ih
      · subst value
        simpa [mergedBindings, extendedBindings, TypedApplyState.advance] using ih

/-- Both directions apply to arbitrary argument lengths, atom trees,
selected binding environments, failed services and raw-argument policies. -/
theorem direct_iff (services : Services) (state : TypedApplyState) (result : ResultPair) :
    result ∈ typedApplyDirect services.evaluate services.apply services.merge
      services.extend services.raw state ↔ Derivation services state result :=
  ⟨direct_sound services state result, direct_complete services⟩

/-- Completing the actual worklist constructs the branch witness. -/
theorem completed_machine_iff (services : Services) (state : TypedApplyState)
    (budget : Nat) (result : ResultPair)
    (done : (machineRun services.evaluate services.apply services.merge services.extend
      services.raw (.initial state) budget).worklist = []) :
    result ∈ (machineRun services.evaluate services.apply services.merge services.extend
      services.raw (.initial state) budget).emitted ↔ Derivation services state result := by
  rw [typedApplyMachine_complete_eq_direct _ _ _ _ _ state budget done]
  exact direct_iff services state result

/-- A source-derived administrative budget realizes every branch and only
those branches. It is independent of the stack runner's execution. -/
theorem work_budget_machine_iff (services : Services) (state : TypedApplyState)
    (result : ResultPair) :
    result ∈ (machineRun services.evaluate services.apply services.merge services.extend
      services.raw (.initial state)
        (typedApplyWork services.evaluate services.apply services.merge services.extend
          services.raw (fun _ _ _ => 0) state)).emitted ↔
      Derivation services state result := by
  rw [typedApplyMachine_work_budget_eq_direct]
  exact direct_iff services state result

end Mettapedia.Languages.MeTTa.HE.TypedApplyDerivation
