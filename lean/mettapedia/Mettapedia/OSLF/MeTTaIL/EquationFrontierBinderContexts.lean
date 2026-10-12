import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileBatches
import Mettapedia.OSLF.MeTTaIL.TypedContextualEquationExecution

/-!
# Licensed conditional execution below an authored binder

The context profile explicitly admits the body of `Nu`. Typing descent adds
its `Name` binder before the original ambient context. The conditional query
projects only its independent guard; the captured cell retains its own binder
dependency. The returned target is plugged into the original outer binder.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderContexts

open Mettapedia.OSLF.MeTTaIL.Syntax DerivedContexts
open Mettapedia.GSLT.LanguageDef.WellSorted
open EquationFrontierBinderProfile

def bindingContext : OneHoleContext := .apply "Nu" [] (.lambda none .hole) []

def permissions : List OneHoleContext := [bindingContext]

theorem ambientContext_succ (ambient : Nat) :
    ambientContext (ambient + 1) = .name :: ambientContext ambient := by
  simp [ambientContext, List.replicate_succ]

def site {ambient : Nat} (state : State (ambient + 1)) :
    TypedContextualEquationExecution.Site language FreeTypeContext.empty
      (ambientContext ambient) .proc permissions (nu state.pattern) where
  context := bindingContext
  focus := state.pattern
  focusBound := ambientContext (ambient + 1)
  focusType := .proc
  permitted := by simp [permissions]
  source_eq := rfl
  typed := by
    apply TypedAt.application (rule := nuRule) (beforeParams := [])
      (afterParams := []) (parameter := .abstraction "body" (.arrow .name .proc))
    · simp [language]
    · simp [UsesBareCollection, nuRule]
    · exact .cons trivial rfl (.lambda (by
        simpa only [← ambientContext_succ, OneHoleContext.fill] using state_typed state)) .nil
    · rfl
    · rfl
    · rfl
    · apply TypedAt.lambda
      apply TypedAt.here
      simpa only [← ambientContext_succ, OneHoleContext.fill] using state_typed state

def execute {ambient : Nat} (allowed : List Token) (state : State (ambient + 1)) :
    TypedContextualEquationExecution.Outcome :=
  TypedContextualEquationExecution.executeSites (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc permissions
    (nu state.pattern) [site state]

/-- Every emitted binder-local receipt uses the full binder context, the
actual atomic conditional derivation and the same surrounding binder. -/
theorem execute_sound {ambient : Nat} (allowed : List Token)
    (state : State (ambient + 1)) (receipt : TypedContextualEquationExecution.Receipt)
    (present : receipt ∈ (execute allowed state).receipts) :
    receipt.context = bindingContext ∧
      receipt.focusBound = ambientContext (ambient + 1) ∧
      receipt.focusType = .proc ∧
      receipt.target = nu receipt.atomic.target ∧
      HasType language FreeTypeContext.empty (ambientContext ambient) receipt.target .proc ∧
      ∃ rule, (rule, receipt.ruleIndex) ∈ language.rewrites.zipIdx ∧
        ConditionalEquationExecution.RuleInstance (provider allowed) language
          FreeTypeContext.empty (ambientContext (ambient + 1)) .proc
          rule state.pattern receipt.atomic := by
  obtain ⟨selected, contextIndex, rule, ruleIndex, chosen, declared, actual⟩ :=
    TypedContextualEquationExecution.executeSites_readout (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc permissions
      (nu state.pattern) [site state] receipt present
  have selectedEq : selected = site state := by
    simpa using List.fst_mem_of_mem_zipIdx chosen
  subst selected
  obtain ⟨atomic, atomicMember, _, contextEq, boundEq, typeEq, indexEq,
    atomicEq, targetEq, _, sorted⟩ :=
    TypedContextualEquationExecution.applyAt_readout (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc permissions
      (nu state.pattern) contextIndex ruleIndex rule (site state) receipt actual
  refine ⟨contextEq, boundEq, typeEq, ?_, sorted, rule, ?_, ?_⟩
  · simpa only [atomicEq, site, bindingContext, OneHoleContext.fill, nu,
      List.nil_append] using targetEq
  · simpa only [indexEq] using declared
  · rw [atomicEq]
    exact ConditionalEquationExecution.applyRuleAtOutcome_sound (provider allowed) language
      FreeTypeContext.empty (ambientContext (ambient + 1)) .proc rule state.pattern atomic atomicMember

def permittedState : State 1 := ⟨.exposed, 0, .permit⟩

theorem fill_finished (ambient : Nat) (index : Fin ((ambient + 1) + 1))
    (token : Token) (declaration resultIndex : Nat) :
    TypedContextualEquationExecution.fillReceipt? language FreeTypeContext.empty
      (ambientContext ambient) .proc 0 declaration bindingContext
      (ambientContext (ambient + 1)) .proc
      (expectedReceipt (ambient + 1) index token .finished resultIndex) =
    some ⟨0, bindingContext, ambientContext (ambient + 1), .proc, declaration,
      expectedReceipt (ambient + 1) index token .finished resultIndex,
      nu (State.pattern (⟨.finished, index, token⟩ : State (ambient + 1)))⟩ := by
  let finished : State (ambient + 1) := ⟨.finished, index, token⟩
  have bodyTyped : HasType language FreeTypeContext.empty
      (.name :: ambientContext ambient) finished.pattern .proc := by
    simpa only [← ambientContext_succ] using state_typed finished
  have targetChecked := checkHasType_complete_of_object
    (nu_typed (ambientContext ambient) finished.pattern bodyTyped)
    (by simp [nu, isObjectPattern, isObjectPatternList, state_object])
  have targetScoped : (nu finished.pattern).isWellScopedAt ambient = true := by
    simpa [nu, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using state_scoped finished
  change TypedContextualEquationExecution.fillReceipt? language FreeTypeContext.empty
      (ambientContext ambient) .proc 0 declaration bindingContext
      (ambientContext (ambient + 1)) .proc
      (expectedReceipt (ambient + 1) index token .finished resultIndex) = _
  simp only [TypedContextualEquationExecution.fillReceipt?, expectedReceipt,
    bindingContext, OneHoleContext.fill, List.nil_append]
  change (if (nu finished.pattern).isWellScopedAt (ambientContext ambient).length &&
    checkHasType language FreeTypeContext.empty (ambientContext ambient)
      (nu finished.pattern) .proc then _ else _) = _
  simp only [ambientContext_length, targetScoped, targetChecked, Bool.and_self, if_true]
  rfl

/-- This run evaluates the actual conditional engine below a binder. -/
theorem two_authored_queries_under_binder :
    (execute [.permit] permittedState).receipts.length = 2 := by
  have root := consume_outcome [.permit] 1 (0 : Fin 2) .permit
  change ConditionalEquationExecution.applyRuleAtOutcome (provider [.permit]) language
    FreeTypeContext.empty (ambientContext 1) .proc consumeRule permittedState.pattern = _ at root
  simp only [execute, TypedContextualEquationExecution.executeSites, language_rewrites,
    List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil,
    TypedContextualEquationExecution.applyAt, site]
  simp only [consume_rename_outcome, root]
  simp [expectedReceipts, fill_finished]

theorem under_binder_query_failure :
    (execute [] permittedState).receipts = [] ∧
      (execute [] permittedState).pending = [] := by
  have root := consume_outcome [] 1 (0 : Fin 2) .permit
  change ConditionalEquationExecution.applyRuleAtOutcome (provider []) language
    FreeTypeContext.empty (ambientContext 1) .proc consumeRule permittedState.pattern = _ at root
  simp only [execute, TypedContextualEquationExecution.executeSites, language_rewrites,
    List.zipIdx_cons, List.zipIdx_nil, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.append_nil,
    TypedContextualEquationExecution.applyAt, site]
  simp only [consume_rename_outcome, root]
  simp [expectedReceipts]

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderContexts
