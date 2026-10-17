import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.AllocationExecution

/-!
# Chronological authority through the original assertion matcher

Successful original assertion traces retain authorized complete entries in
all physical slots, including constructor reservations and fills. A pointer
comparison becomes a complete payload comparison only after both entries
have this independently earned chronological authority.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MM0.MeTTa.MMBMatchAuthority

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open ListAccess (listValue optionValue)
open Store (natural)
open MMBProofRunExecution (expressionValue)
open MMBAllocationExecution
open MMBRecursiveMatchExecution
open Kernel (Preterm)
open Effects (State)
open Eval

abbrev program := MMBRecursiveMatchExecution.program

/-- Complete original constructor fields, including the ordered children and
resolved logical constructor ID. This refines original atoms only. -/
def EntryFields (history : List Atom) (entry : Atom) : Prop :=
  (∃ pointer index, entry = variableEntry pointer index) ∨
  ∃ pointer binary identifier arguments values,
    entry = applicationEntry pointer binary identifier arguments values ∧
    (∀ argument ∈ arguments, AuthorizedExpression history argument) ∧
    MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm)

theorem EntryFields.append {history suffix : List Atom} {entry : Atom}
    (fields : EntryFields history entry) : EntryFields (history ++ suffix) entry := by
  rcases fields with variableFields | ⟨pointer, binary, identifier, arguments, values, same, authorized, projected⟩
  · exact .inl variableFields
  · exact .inr ⟨pointer, binary, identifier, arguments, values, same,
      fun argument member => (authorized argument member).append, projected⟩

/-- Every original constructed allocation retains its complete argument
projections and their authority in the entire current history. -/
theorem constructed_fields {history : List Atom} (built : ConstructedHistory history) :
    ∀ entry ∈ history, EntryFields history entry := by
  induction built with
  | empty => intro entry impossible; cases impossible
  | @variableNode history built index ih =>
      intro entry member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact (ih entry member).append
      · exact .inl ⟨history.length, index, rfl⟩
  | @application history built binary identifier arguments values authorized projected ih =>
      intro entry member
      simp only [List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact (ih entry member).append
      · exact .inr ⟨history.length, binary, identifier, arguments, values, rfl,
          fun argument member => (authorized argument member).append, projected⟩

theorem authorized_fields {history : List Atom} {entry : Atom}
    (authorized : AuthorizedExpression history entry) (built : ConstructedHistory history) :
    EntryFields history entry := by
  obtain ⟨pointer, value, node, shape, found⟩ := authorized
  exact constructed_fields built entry (List.mem_of_getElem? found)

/-- Original application entry fields determine every child, its preterm
projection, and the complete resolved application value. -/
theorem application_fields {history children : List Atom}
    {pointer binary : Nat} {value : Atom}
    (authorized : AuthorizedExpression history
      (expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural binary, listValue children])))
    (built : ConstructedHistory history) :
    ∃ identifier values,
      value = Data.preterm (Preterm.applyArgs (.term identifier) values) ∧
      (∀ child ∈ children, AuthorizedExpression history child) ∧
      MMBProofRunExecution.ExpressionClaims children (values.map Data.preterm) := by
  rcases authorized_fields authorized built with ⟨allocation, index, same⟩ |
      ⟨allocation, originalBinary, identifier, arguments, values, same, childrenAuthorized, projected⟩
  · simp [variableEntry, expressionValue, listValue] at same
  · have fields : value = Data.preterm (Preterm.applyArgs (.term identifier) values) ∧ children = arguments := by
      simp only [applicationEntry, expressionValue, listValue, Atom.expression.injEq, List.cons.injEq,
        and_true, true_and] at same
      exact ⟨same.2.1, same.2.2.2⟩
    obtain ⟨valueSame, rfl⟩ := fields
    exact ⟨identifier, values, valueSame, childrenAuthorized, projected⟩

/-- An unavailable original reservation or a complete authorized expression. -/
def SlotAuthorized (history : List Atom) (slot : Atom) : Prop :=
  slot = .symbol "None" ∨
    ∃ entry, slot = optionValue (some entry) ∧ AuthorizedExpression history entry

def SlotsAuthorized (history slots : List Atom) : Prop :=
  ∀ slot ∈ slots, SlotAuthorized history slot

theorem SlotsAuthorized.wellFormed {history slots : List Atom}
    (authorized : SlotsAuthorized history slots) : SlotsWellFormed slots := by
  intro slot member
  rcases authorized slot member with unavailable | ⟨entry, same, pointer, value, node, shape, found⟩
  · exact .inl unavailable
  · exact .inr ⟨pointer, value, node, by rw [same, shape]⟩

theorem SlotsAuthorized.initial {history arguments : List Atom}
    (authorized : ∀ argument ∈ arguments, AuthorizedExpression history argument) :
    SlotsAuthorized history (MMBAssertionMatchExecution.initialSlots arguments) := by
  intro slot member
  simp only [MMBAssertionMatchExecution.initialSlots] at member
  obtain ⟨argument, inArguments, same⟩ := List.mem_map.mp member
  exact .inr ⟨argument, same.symm, authorized argument inArguments⟩

theorem SlotsAuthorized.reserve {history slots : List Atom}
    (authorized : SlotsAuthorized history slots) (save : Bool) :
    SlotsAuthorized history (reservedSlots save slots) := by
  cases save
  · exact authorized
  · intro slot member
    simp only [reservedSlots, if_true, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · exact authorized slot member
    · exact .inl rfl

theorem SlotsAuthorized.set {history slots : List Atom} (authorized : SlotsAuthorized history slots)
    (index : Nat) (entry : Atom) (entryAuthorized : AuthorizedExpression history entry) :
    SlotsAuthorized history (slots.set index (optionValue (some entry))) := by
  intro slot member
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact authorized slot member
  · exact .inr ⟨entry, rfl, entryAuthorized⟩

theorem SlotAuthorized.some {history : List Atom} {entry : Atom}
    (authorized : SlotAuthorized history (optionValue (some entry))) : AuthorizedExpression history entry := by
  rcases authorized with unavailable | ⟨original, same, authorized⟩
  · simp [optionValue] at unavailable
  · have sameEntry : entry = original := by simpa [optionValue] using same
    simpa only [sameEntry] using authorized

/-- The original reservation/fill operation keeps authority whenever it
succeeds; no unavailable physical reservation is invented. -/
theorem finishedMatch_authorized {history slots after rest final unread : List Atom} {target : Atom}
    (save : Bool) (slotsAuthorized : SlotsAuthorized history after)
    (targetAuthorized : AuthorizedExpression history target)
    (accepted : finishedMatch save slots target (some (after, rest)) = some (final, unread)) :
    SlotsAuthorized history final := by
  cases save with
  | false =>
      simp only [finishedMatch, Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact slotsAuthorized
  | true =>
      simp only [finishedMatch, if_true] at accepted
      cases found : after[slots.length]? with
      | none => simp [found] at accepted
      | some reserved =>
          simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact slotsAuthorized.set slots.length target targetAuthorized

private theorem match_authority (history : List Atom) (built : ConstructedHistory history)
    (images context resolver : Atom) (fuel : Nat) :
    (∀ slots codes target result, ExpressionMatch images context resolver fuel slots codes target result →
      SlotsAuthorized history slots → AuthorizedExpression history target →
      ∀ after rest, result = some (after, rest) → SlotsAuthorized history after) ∧
    (∀ slots codes children result, ExpressionListMatch images context resolver fuel slots codes children result →
      SlotsAuthorized history slots → (∀ child ∈ children, AuthorizedExpression history child) →
      ∀ after rest, result = some (after, rest) → SlotsAuthorized history after) := by
  induction fuel with
  | zero =>
      constructor
      · intro slots codes target result trace authorized targetAuthorized after rest accepted
        cases trace with
        | zero => simp at accepted
      · intro slots codes children result trace authorized childrenAuthorized after rest accepted
        cases trace with
        | empty => cases accepted; exact authorized
        | zero => simp at accepted
  | succ fuel ih =>
      constructor
      · intro slots codes target result trace authorized targetAuthorized after rest accepted
        cases trace with
        | emptyCodes => simp at accepted
        | unknown => simp at accepted
        | wrongConstructor => simp at accepted
        | variableConstructor => simp at accepted
        | dummyVariable => simp at accepted
        | dummyApplication => simp at accepted
        | reference _ pointer index start endPointer stored _ unread expression node value shape found =>
            by_cases same : stored = pointer
            · simp only [same, if_true, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact authorized
            · simp [same] at accepted
        | unavailable => simp at accepted
        | constructor _ pointer term start endPointer save _ unread children value child matched =>
            obtain ⟨identifier, values, _, childrenAuthorized, _⟩ := application_fields targetAuthorized built
            cases child with
            | none => simp [finishedMatch] at accepted
            | some pair =>
                obtain ⟨middle, remaining⟩ := pair
                have intermediate := ih.2 _ _ _ _ matched (authorized.reserve save) childrenAuthorized middle remaining rfl
                exact finishedMatch_authorized save intermediate targetAuthorized accepted
      · intro slots codes children result trace authorized childrenAuthorized after rest accepted
        cases trace with
        | empty => cases accepted; exact authorized
        | refused => simp at accepted
        | next _ _ _ intermediate unread first remaining _ matched continued =>
            have firstAuthorized := childrenAuthorized first (by simp)
            have nextAuthorized := ih.1 _ _ _ _ matched authorized firstAuthorized intermediate unread rfl
            exact ih.2 _ _ _ _ continued nextAuthorized (fun child member => childrenAuthorized child (by simp [member])) after rest accepted

/-- All original recursive constructor matches preserve authorized complete
slots, including optional parent reservations before child traversal. -/
theorem expression_authorized_slots {history : List Atom} (built : ConstructedHistory history)
    (images context resolver : Atom) (fuel : Nat) (slots codes : List Atom) (target : Atom)
    (after rest : List Atom) (trace : ExpressionMatch images context resolver fuel slots codes target (some (after, rest)))
    (slotsAuthorized : SlotsAuthorized history slots) (targetAuthorized : AuthorizedExpression history target) :
    SlotsAuthorized history after :=
  (match_authority history built images context resolver fuel).1 _ _ _ _ trace slotsAuthorized targetAuthorized after rest rfl

theorem children_authorized_slots {history : List Atom} (built : ConstructedHistory history)
    (images context resolver : Atom) (fuel : Nat) (slots codes children after rest : List Atom)
    (trace : ExpressionListMatch images context resolver fuel slots codes children (some (after, rest)))
    (slotsAuthorized : SlotsAuthorized history slots)
    (childrenAuthorized : ∀ child ∈ children, AuthorizedExpression history child) : SlotsAuthorized history after :=
  (match_authority history built images context resolver fuel).2 _ _ _ _ trace slotsAuthorized childrenAuthorized after rest rfl

/-- Authorized original pointer references agree in both complete fields. -/
theorem reference_payload (history slots : List Atom) (index pointer stored : Nat)
    (targetValue targetNode storedValue storedNode : Atom) (authorized : SlotsAuthorized history slots)
    (targetAuthorized : AuthorizedExpression history (expressionValue pointer targetValue targetNode))
    (found : slots[index]? = some (optionValue (some (expressionValue stored storedValue storedNode))))
    (same : stored = pointer) : targetValue = storedValue ∧ targetNode = storedNode := by
  have storedAuthorized := (authorized _ (List.mem_of_getElem? found)).some
  subst stored
  exact authorized_pointer_unique history pointer _ _ _ _ targetAuthorized storedAuthorized

/-- If those payloads are original kernel preterms, the unchanged source's
identity comparison also establishes equality of their complete preterms. -/
theorem reference_preterm (history slots : List Atom) (index pointer stored : Nat)
    (target storedExpression : Preterm) (targetNode storedNode : Atom) (authorized : SlotsAuthorized history slots)
    (targetAuthorized : AuthorizedExpression history (expressionValue pointer (Data.preterm target) targetNode))
    (found : slots[index]? = some (optionValue (some (expressionValue stored (Data.preterm storedExpression) storedNode))))
    (same : stored = pointer) : target = storedExpression :=
  Data.preterm_injective (reference_payload history slots index pointer stored _ _ _ _ authorized targetAuthorized found same).1

private theorem hypothesis_authority (history : List Atom) (built : ConstructedHistory history)
    (images context resolver : Atom) (fuel : Nat) :
    ∀ slots codes targets result, HypothesisMatch images context resolver fuel slots codes targets result →
      SlotsAuthorized history slots → (∀ target ∈ targets, AuthorizedExpression history target) →
      ∀ after, result = some after → SlotsAuthorized history after := by
  induction fuel with
  | zero =>
      intro slots codes targets result trace authorized targetsAuthorized after accepted
      cases trace with
      | empty => cases accepted; exact authorized
      | missingCode => simp at accepted
      | extraCode => simp at accepted
      | wrongBoundary => simp at accepted
      | zero => simp at accepted
  | succ fuel ih =>
      intro slots codes targets result trace authorized targetsAuthorized after accepted
      cases trace with
      | empty => cases accepted; exact authorized
      | missingCode => simp at accepted
      | extraCode => simp at accepted
      | wrongBoundary => simp at accepted
      | refused => simp at accepted
      | next _ data start endPointer slots codes intermediate unread first earlier result matched remaining =>
          have nextAuthorized := expression_authorized_slots built images context resolver fuel slots codes first
            intermediate unread matched authorized (targetsAuthorized first (by simp))
          exact ih intermediate unread earlier result remaining nextAuthorized
            (fun target member => targetsAuthorized target (by simp [member])) after accepted

/-- Original hypothesis traversal carries the same complete-entry authority
through each ordered assertion match and its physical slot continuation. -/
theorem hypotheses_authorized_slots {history : List Atom} (built : ConstructedHistory history)
    (images context resolver : Atom) (fuel : Nat) (slots codes targets after : List Atom)
    (trace : HypothesisMatch images context resolver fuel slots codes targets (some after))
    (slotsAuthorized : SlotsAuthorized history slots)
    (targetsAuthorized : ∀ target ∈ targets, AuthorizedExpression history target) : SlotsAuthorized history after :=
  hypothesis_authority history built images context resolver fuel slots codes targets (some after)
    trace slotsAuthorized targetsAuthorized after rfl

/-- Filled authorized slots contain an original kernel preterm and retain the
complete entry supplying it. -/
theorem SlotsAuthorized.preterms {history slots : List Atom} (built : ConstructedHistory history)
    (authorized : SlotsAuthorized history slots) (index : Nat) (entry : Atom)
    (found : slots[index]? = some (optionValue (some entry))) :
    ∃ pointer expression node, entry = expressionValue pointer (Data.preterm expression) node := by
  have entryAuthorized := (authorized _ (List.mem_of_getElem? found)).some
  obtain ⟨pointer, value, node, same, position⟩ := entryAuthorized
  exact built.preterms entry (List.mem_of_getElem? position)

/-- Arbitrary well-shaped original expression calls terminate with the exact
source result or refusal. Every completed success retains slot authority. -/
theorem expression_completed_authority {history : List Atom} (built : ConstructedHistory history)
    (state : State) (images : List Atom) (context resolver : Atom) (fuel : Nat)
    (slots codes : List Atom) (target : Atom) (slotsAuthorized : SlotsAuthorized history slots)
    (codesShape : CodesWellFormed codes) (targetAuthorized : AuthorizedExpression history target) :
    ∃ result,
      (∀ after rest, result = some (after, rest) → SlotsAuthorized history after) ∧
      ∀ after answers input output,
        (∃ budget, run program budget
          {state := state, control := .evaluate
            (callBindings fuel (MMBAssertionMatchExecution.matchingValue slots (listValue images) context resolver) (listValue codes) target)
            (callExpression "mm0:mmb:match-expression")} = .complete after answers input output) ↔
        after = state ∧ answers = [resultValue (listValue images) context resolver result] ∧ input = [] ∧ output = [] := by
  obtain ⟨result, trace, _⟩ := expression_total images context resolver fuel slots codes target
    slotsAuthorized.wellFormed codesShape (targetAuthorized.shape built)
  refine ⟨result, ?_, ?_⟩
  · intro after rest accepted
    exact (match_authority history built (listValue images) context resolver fuel).1 _ _ _ _ trace
      slotsAuthorized targetAuthorized after rest accepted
  · intro after answers input output
    exact pure_returns_completed_iff program _ state state _ _
      (expression_returns state (listValue images) context resolver fuel slots codes target result trace) after answers input output

/-- Arbitrary original child calls retain each occurrence and its complete
entry authority while qualifying every completed success or refusal. -/
theorem children_completed_authority {history : List Atom} (built : ConstructedHistory history)
    (state : State) (images : List Atom) (context resolver : Atom) (fuel : Nat)
    (slots codes children : List Atom) (slotsAuthorized : SlotsAuthorized history slots)
    (codesShape : CodesWellFormed codes) (childrenAuthorized : ∀ child ∈ children, AuthorizedExpression history child) :
    ∃ result,
      (∀ after rest, result = some (after, rest) → SlotsAuthorized history after) ∧
      ∀ after answers input output,
        (∃ budget, run program budget
          {state := state, control := .evaluate
            (callBindings fuel (MMBAssertionMatchExecution.matchingValue slots (listValue images) context resolver) (listValue codes) (listValue children))
            (callExpression "mm0:mmb:match-expressions")} = .complete after answers input output) ↔
        after = state ∧ answers = [resultValue (listValue images) context resolver result] ∧ input = [] ∧ output = [] := by
  obtain ⟨result, trace, _⟩ := children_total images context resolver fuel slots codes children
    slotsAuthorized.wellFormed codesShape (fun child member => (childrenAuthorized child member).shape built)
  refine ⟨result, ?_, ?_⟩
  · intro after rest accepted
    exact (match_authority history built (listValue images) context resolver fuel).2 _ _ _ _ trace
      slotsAuthorized childrenAuthorized after rest accepted
  · intro after answers input output
    exact pure_returns_completed_iff program _ state state _ _
      (children_returns state (listValue images) context resolver fuel slots codes children result trace) after answers input output

/-- The complete original hypothesis matcher has the same authority law,
including every command boundary and its explicit refusal result. -/
theorem hypotheses_completed_authority {history : List Atom} (built : ConstructedHistory history)
    (state : State) (images : List Atom) (context resolver : Atom) (fuel : Nat)
    (slots codes targets : List Atom) (slotsAuthorized : SlotsAuthorized history slots)
    (codesShape : CodesWellFormed codes) (targetsAuthorized : ∀ target ∈ targets, AuthorizedExpression history target) :
    ∃ result,
      (∀ after, result = some after → SlotsAuthorized history after) ∧
      ∀ after answers input output,
        (∃ budget, run program budget
          {state := state, control := .evaluate
            (callBindings fuel (MMBAssertionMatchExecution.matchingValue slots (listValue images) context resolver) (listValue codes) (listValue targets))
            (callExpression "mm0:mmb:match-hypotheses")} = .complete after answers input output) ↔
        after = state ∧ answers = [hypothesisValue (listValue images) context resolver result] ∧ input = [] ∧ output = [] := by
  obtain ⟨result, trace, _⟩ := hypotheses_total images context resolver fuel slots codes targets
    slotsAuthorized.wellFormed codesShape (fun target member => (targetsAuthorized target member).shape built)
  refine ⟨result, ?_, ?_⟩
  · intro after accepted
    exact hypothesis_authority history built (listValue images) context resolver fuel slots codes targets result
      trace slotsAuthorized targetsAuthorized after accepted
  · intro after answers input output
    exact pure_returns_completed_iff program _ state state _ _
      (hypotheses_returns state (listValue images) context resolver fuel slots codes targets result trace) after answers input output

/-- A completed original reference match implies equality of full kernel
preterms when both entries have chronological authority. Equal labels from
untrusted external entries do not satisfy that hypothesis. -/
theorem reference_accepted_preterm (history slots : List Atom) (state : State) (images context resolver : Atom)
    (fuel index pointer stored start endPointer : Nat) (rest : List Atom)
    (target storedExpression : Preterm) (targetNode storedNode : Atom) (authorized : SlotsAuthorized history slots)
    (targetAuthorized : AuthorizedExpression history (expressionValue pointer (Data.preterm target) targetNode))
    (found : slots[index]? = some (optionValue (some (expressionValue stored (Data.preterm storedExpression) storedNode))))
    (observed : ∃ budget, run program budget
      {state := state, control := .evaluate
        (callBindings (fuel + 1) (MMBAssertionMatchExecution.matchingValue slots images context resolver)
          (listValue (MMBExecution.commandValue 50 index start endPointer :: rest))
          (expressionValue pointer (Data.preterm target) targetNode))
        (callExpression "mm0:mmb:match-expression")} =
      .complete state [MMBAssertionMatchExecution.matchedValue slots images context resolver rest] [] []) :
    target = storedExpression := by
  have trace := ExpressionMatch.reference (images := images) (context := context) (resolver := resolver)
    fuel pointer index start endPointer stored slots rest (Data.preterm target) targetNode
    (Data.preterm storedExpression) storedNode found
  have result := (expression_result_iff state images context resolver (fuel + 1) slots _ _ _ _ trace).mp observed
  by_cases same : stored = pointer
  · exact reference_preterm history slots index pointer stored target storedExpression targetNode storedNode
      authorized targetAuthorized found same
  · simp [same, resultValue, MMBAssertionMatchExecution.matchedValue, optionValue] at result

end Mettapedia.Languages.MM0.MeTTa.MMBMatchAuthority
