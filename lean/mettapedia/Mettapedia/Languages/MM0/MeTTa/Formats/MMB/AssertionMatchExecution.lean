import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.SlotExecution
import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.TheoremCommandExecution

/-!
# Original assertion-mode binary matching

Slot preparation preserves every supplied expression entry. Reference
instructions compare original allocation identities; equal expression payloads
do not replace that pointer check. The laws concern the unchanged quoted MMB
programme and preserve its actual matching state and unread command suffix.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBAssertionMatchExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (expressionValue)

abbrev program := MMBTheoremExecution.program

private def sourceEquation (head : String) : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == head)).head?).getD
    ⟨"", [], .symbol "None"⟩
private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

/-- Original slots contain explicit optional entries in the supplied order. -/
def initialSlots (arguments : List Atom) : List Atom := arguments.map fun argument => optionValue (some argument)

/-- The exact original assertion-mode matching state; fields remain inert. -/
def matchingValue (slots : List Atom) (images context resolver : Atom) : Atom :=
  .expression [.symbol "MM0:MMBMState", listValue slots, images, context, resolver, .symbol "MM0:MMBAssertionMatch"]

def matchedValue (slots : List Atom) (images context resolver : Atom) (rest : List Atom) : Atom :=
  optionValue (some (.expression [.symbol "MM0:MMBMatched", matchingValue slots images context resolver, listValue rest]))

private def slotsEquation := sourceEquation "mm0:mmb:match-slots"
private def slotsCases := casesOf slotsEquation.body
private def slotsCons := (slotsCases[1]'(by decide)).2
private def slotsEnvironment (arguments : List Atom) : Subst := [("arguments", .expression arguments)]
private theorem slots_unique : program.equations.filter (·.head == "mm0:mmb:match-slots") = [slotsEquation] := by
  decide +kernel
private theorem slots_formals : slotsEquation.arguments = [.expression [.symbol "MM0:L", .var "arguments"]] := by decide
private theorem slots_shape : slotsEquation.body = .expression [.symbol "case", .var "arguments",
    .expression (slotsCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem slots_cases_shape : slotsCases =
    [(.expression [], .expression [.symbol "MM0:L", .expression []]),
     (.expression [.symbol "cons", .var "first", .var "rest"], slotsCons),
     (.var "bad", .symbol "MM0:Malformed")] := by decide
private theorem slots_cons_shape : slotsCons = .expression [.symbol "let", .var "tail",
    .expression [.symbol "mm0:mmb:match-slots", .expression [.symbol "MM0:L", .var "rest"]],
    .expression [.symbol "mm0:list-cons", .expression [.symbol "Some", .var "first"], .var "tail"]] := by decide
private theorem slots_clause (arguments : List Atom) :
    clauses program "mm0:mmb:match-slots" [listValue arguments] =
      [.evaluate (slotsEnvironment arguments) slotsEquation.body] := by
  rw [clauses_use_only_the_named_equations, slots_unique]
  simp [slots_formals, slotsEnvironment, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem slots_from_body (bindings : Subst) (state : State) (arguments : List Atom) (argument : Atom)
    (captured : applySubst bindings argument = listValue arguments)
    (body : PureReturns program (slotsEnvironment arguments) state slotsEquation.body state (listValue (initialSlots arguments))) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:match-slots", argument]) state
      (listValue (initialSlots arguments)) := by
  apply raw_call_returns program bindings state state "mm0:mmb:match-slots" [argument] _
    (by decide +kernel) _ _ (by decide)
  · intro offset bounded
    have same : offset = 0 := by simpa using bounded
    subst offset
    decide +kernel
  · simpa only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, captured] using
      authored_function_arguments_return program bindings (slotsEnvironment arguments) state state "mm0:mmb:match-slots"
        [listValue arguments] 1 slotsEquation.body _ (by decide +kernel) (by decide) (slots_clause arguments) body

private theorem slots_body_returns (state : State) (arguments : List Atom) :
    PureReturns program (slotsEnvironment arguments) state slotsEquation.body state (listValue (initialSlots arguments)) := by
  induction arguments with
  | nil =>
      rw [slots_shape]
      apply case_returns program (slotsEnvironment []) (slotsEnvironment []) state state state
        (.var "arguments") (.expression []) (.expression [.symbol "MM0:L", .expression []]) _ _ slotsCases
        (read_cases_encoded slotsCases)
      · exact variable_returns program _ state "arguments"
      · simp [slots_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, slotsEnvironment]
      · simpa [initialSlots, listValue] using empty_constructor_returns program (slotsEnvironment []) state "MM0:L"
          (by decide +kernel) (by decide)
  | cons first rest ih =>
      let bindings := slotsEnvironment (first :: rest)
      let bound := ("rest", .expression rest) :: ("first", first) :: bindings
      let tailed := ("tail", listValue (initialSlots rest)) :: bound
      rw [slots_shape]
      apply case_returns program bindings bound state state state (.var "arguments") (.expression (first :: rest))
        slotsCons _ _ slotsCases (read_cases_encoded slotsCases)
      · exact variable_returns program _ state "arguments"
      · simp [slots_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, bound, bindings, slotsEnvironment]
      · rw [slots_cons_shape]
        apply let_returns program bound tailed state state state (.var "tail") _ _ (listValue (initialSlots rest)) _
        · apply slots_from_body bound state rest (.expression [.symbol "MM0:L", .var "rest"]) _ ih
          simp [bound, bindings, slotsEnvironment, listValue, applySubst, applySubst.applySubstList, Subst.lookup]
        · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, tailed, bound, bindings, slotsEnvironment]
        · let prior : Subst := [("head", optionValue (some first)), ("tail", listValue (initialSlots rest))]
          have returned := MMBProofRunExecution.checker_returns (by decide +kernel)
            (ListAccess.cons_captured_returns prior state (optionValue (some first)) (initialSlots rest) "head" "tail" rfl rfl)
          apply captured_call_returns program prior tailed state state "mm0:list-cons"
            [.var "head", .var "tail"] [.expression [.symbol "Some", .var "first"], .var "tail"] _
            (by decide +kernel) (by decide) _ _ _ (by simpa only [initialSlots, List.map_cons] using returned)
          · intro offset argument found
            have bounded : offset < 2 := by
              have inside := (getElem?_eq_some_iff.mp found).choose
              simpa using inside
            interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
          · intro offset argument found
            have bounded : offset < 2 := by
              have inside := (getElem?_eq_some_iff.mp found).choose
              simpa using inside
            interval_cases offset
            · left; decide +kernel
            · simp at found; subst argument; right; rfl
          · simp [prior, tailed, bound, bindings, slotsEnvironment, optionValue,
              applySubst, applySubst.applySubstList, Subst.lookup]

/-- The original matcher creates one slot for every physical argument,
retaining order, duplicates and arbitrary inert field contents. -/
theorem match_slots_returns (bindings : Subst) (state : State) (arguments : List Atom) (argument : Atom)
    (captured : applySubst bindings argument = listValue arguments) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:match-slots", argument]) state
      (listValue (initialSlots arguments)) :=
  slots_from_body bindings state arguments argument captured (slots_body_returns state arguments)

private def expressionEquation := sourceEquation "mm0:mmb:match-expression"
private def expressionElse := match expressionEquation.body with | .expression [_, _, body, _] => body | _ => .symbol "None"
private def expressionCases := casesOf expressionElse
private def opcodeBody := (expressionCases[0]'(by decide)).2
private def opcodeCases := casesOf opcodeBody
private def referenceBody := (opcodeCases[2]'(by decide)).2
private def noSaveTermBody := (opcodeCases[0]'(by decide)).2
private def saveTermBody := (opcodeCases[1]'(by decide)).2
private def dummyBody := (opcodeCases[3]'(by decide)).2
private def referenceCases := casesOf referenceBody
private def referenceFound := (referenceCases[0]'(by decide)).2
private def referenceTrue := match referenceFound with | .expression [_, _, body, _] => body | _ => .symbol "None"

private def expressionEnvironment (fuel pointer : Nat) (slots codes : List Atom)
    (images context resolver expression node : Atom) : Subst :=
  [("node", node), ("expression", expression), ("pointer", natural pointer), ("codes", .expression codes),
    ("mode", .symbol "MM0:MMBAssertionMatch"), ("resolver", resolver), ("context", context), ("images", images),
    ("slots", .expression slots), ("fuel", natural fuel)]
private def referenceEnvironment (fuel pointer index start after : Nat) (slots rest : List Atom)
    (images context resolver expression node : Atom) : Subst :=
  ("rest", .expression rest) :: ("after", natural after) :: ("start", natural start) ::
    ("data", natural index) :: ("opcode", natural 50) ::
    expressionEnvironment (fuel + 1) pointer slots (MMBExecution.commandValue 50 index start after :: rest)
      images context resolver expression node

private theorem expression_unique : program.equations.filter (·.head == "mm0:mmb:match-expression") = [expressionEquation] := by
  decide +kernel
private theorem expression_formals : expressionEquation.arguments =
    [.var "fuel", .expression [.symbol "MM0:MMBMState", .expression [.symbol "MM0:L", .var "slots"],
      .var "images", .var "context", .var "resolver", .var "mode"],
     .expression [.symbol "MM0:L", .var "codes"],
     .expression [.symbol "MM0:MMBExpression", .var "pointer", .var "expression", .var "node"]] := by decide
private theorem expression_shape : expressionEquation.body = .expression [.symbol "if",
    .expression [.symbol "<", natural 0, .var "fuel"], expressionElse, .symbol "None"] := by decide
private theorem expression_else_shape : expressionElse = .expression [.symbol "case", .var "codes",
    .expression (expressionCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem expression_cases_shape : expressionCases =
    [(.expression [.symbol "cons", .expression [.symbol "MM0:MMBCode", .var "opcode", .var "data", .var "start", .var "after"],
       .var "rest"], opcodeBody), (.var "bad", .symbol "None")] := by decide
private theorem opcode_shape : opcodeBody = .expression [.symbol "case", .var "opcode",
    .expression (opcodeCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem reference_case_present : opcodeCases[2]? = some (natural 50, referenceBody) := by decide
private theorem opcode_cases_shape : opcodeCases =
    [(natural 48, noSaveTermBody), (natural 49, saveTermBody), (natural 50, referenceBody),
     (natural 51, dummyBody), (.var "bad", .symbol "None")] := by decide
private theorem reference_shape : referenceBody = .expression [.symbol "case",
    .expression [.symbol "mm0:data-at", .expression [.symbol "MM0:L", .var "slots"], .var "data"],
    .expression (referenceCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem reference_cases_shape : referenceCases =
    [(.expression [.symbol "Some", .expression [.symbol "Some", .expression [.symbol "MM0:MMBExpression",
       .var "stored", .var "value", .var "shape"]]], referenceFound), (.var "bad", .symbol "None")] := by decide
private theorem reference_found_shape : referenceFound = .expression [.symbol "if",
    .expression [.symbol "==", .var "stored", .var "pointer"], referenceTrue, .symbol "None"] := by decide
private theorem reference_true_shape : referenceTrue = .expression [.symbol "Some",
    .expression [.symbol "MM0:MMBMatched",
      .expression [.symbol "MM0:MMBMState", .expression [.symbol "MM0:L", .var "slots"],
        .var "images", .var "context", .var "resolver", .var "mode"],
      .expression [.symbol "MM0:L", .var "rest"]]] := by decide

private theorem expression_clause (fuel pointer : Nat) (slots codes : List Atom)
    (images context resolver expression node : Atom) :
    clauses program "mm0:mmb:match-expression"
      [natural fuel, matchingValue slots images context resolver, listValue codes, expressionValue pointer expression node] =
      [.evaluate (expressionEnvironment fuel pointer slots codes images context resolver expression node) expressionEquation.body] := by
  rw [clauses_use_only_the_named_equations, expression_unique]
  simp [expression_formals, matchingValue, expressionValue, expressionEnvironment, listValue,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem matching_constructor_returns (bindings : Subst) (state : State) (slots : List Atom)
    (images context resolver : Atom)
    (slotsCaptured : applySubst bindings (.var "slots") = .expression slots)
    (imagesCaptured : applySubst bindings (.var "images") = images)
    (contextCaptured : applySubst bindings (.var "context") = context)
    (resolverCaptured : applySubst bindings (.var "resolver") = resolver)
    (modeCaptured : applySubst bindings (.var "mode") = .symbol "MM0:MMBAssertionMatch") :
    PureReturns program bindings state (.expression [.symbol "MM0:MMBMState",
      .expression [.symbol "MM0:L", .var "slots"], .var "images", .var "context", .var "resolver", .var "mode"])
      state (matchingValue slots images context resolver) := by
  apply data_call_returns program bindings state state "MM0:MMBMState" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data (.symbol "MM0:MMBMState")
    (.symbol "MM0:MMBMState") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:MMBMState")
  apply evaluated_argument_returns program bindings state state state .data
    (.expression [.symbol "MM0:L", .var "slots"]) (listValue slots) _ _ [.symbol "MM0:MMBMState"] 1 rfl
  · simpa [slotsCaptured, listValue] using unary_constructor_returns program bindings state "MM0:L" "slots"
      (by decide +kernel) (by decide)
  · simpa [slotsCaptured, imagesCaptured, contextCaptured, resolverCaptured, modeCaptured, matchingValue] using
      variable_arguments_return program bindings state state .data ["images", "context", "resolver", "mode"]
        [.symbol "MM0:MMBMState", listValue slots] 2 (matchingValue slots images context resolver)
        (by simpa [matchingValue, imagesCaptured, contextCaptured, resolverCaptured, modeCaptured] using
          data_arguments_values_return program bindings state [.symbol "MM0:MMBMState",
          listValue slots, images, context, resolver, .symbol "MM0:MMBAssertionMatch"] 6)

private theorem reference_true_returns (state : State) (fuel pointer index start after stored : Nat)
    (slots rest : List Atom) (images context resolver expression node value shape : Atom) :
    PureReturns program (("shape", shape) :: ("value", value) :: ("stored", natural stored) ::
      referenceEnvironment fuel pointer index start after slots rest images context resolver expression node)
      state referenceTrue state (matchedValue slots images context resolver rest) := by
  let bindings := ("shape", shape) :: ("value", value) :: ("stored", natural stored) ::
    referenceEnvironment fuel pointer index start after slots rest images context resolver expression node
  rw [reference_true_shape]
  apply unary_constructor_of_returns program bindings state state "Some" _ _ (by decide +kernel) (by decide)
  apply binary_constructor_returns program bindings state state state "MM0:MMBMatched" _ _
    (matchingValue slots images context resolver) (listValue rest) (by decide +kernel) (by decide)
  · apply matching_constructor_returns <;> simp [bindings, referenceEnvironment, expressionEnvironment,
      applySubst, Subst.lookup]
  · simpa [bindings, referenceEnvironment, listValue, applySubst, Subst.lookup] using
      unary_constructor_returns program bindings state "MM0:L" "rest" (by decide +kernel) (by decide)

private theorem reference_read_returns (state : State) (fuel pointer index start after : Nat)
    (slots rest : List Atom) (images context resolver expression node : Atom) :
    PureReturns program (referenceEnvironment fuel pointer index start after slots rest images context resolver expression node)
      state (.expression [.symbol "mm0:data-at", .expression [.symbol "MM0:L", .var "slots"], .var "data"])
      state (optionValue (slots[index]?)) := by
  let bindings := referenceEnvironment fuel pointer index start after slots rest images context resolver expression node
  let prior : Subst := [("slots", listValue slots), ("index", natural index)]
  have returned := MMBProofRunExecution.checker_returns (by decide +kernel)
    (ListAccess.data_at_list_returns prior state slots index "slots" "index" rfl rfl)
  apply captured_call_returns program prior bindings state state "mm0:data-at"
    [.var "slots", .var "index"] [.expression [.symbol "MM0:L", .var "slots"], .var "data"] _
    (by decide +kernel) (by decide) _ _ _ returned
  · intro offset argument found
    have bounded : offset < 2 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    interval_cases offset <;> simp at found <;> subst argument <;> right <;> rfl
  · intro offset argument found
    have bounded : offset < 2 := by
      have inside := (getElem?_eq_some_iff.mp found).choose
      simpa using inside
    interval_cases offset
    · left; decide +kernel
    · simp at found; subst argument; right; rfl
  · simp [prior, bindings, referenceEnvironment, expressionEnvironment, applySubst, applySubst.applySubstList,
      Subst.lookup, listValue]

private theorem expression_reference_from_body (state : State) (fuel pointer index start after : Nat)
    (slots rest : List Atom) (images context resolver expression node answer : Atom)
    (body : PureReturns program (referenceEnvironment fuel pointer index start after slots rest images context resolver expression node)
      state referenceBody state answer) :
    PureReturns program (expressionEnvironment (fuel + 1) pointer slots
      (MMBExecution.commandValue 50 index start after :: rest) images context resolver expression node)
      state expressionEquation.body state answer := by
  let bindings := expressionEnvironment (fuel + 1) pointer slots
    (MMBExecution.commandValue 50 index start after :: rest) images context resolver expression node
  let bound := referenceEnvironment fuel pointer index start after slots rest images context resolver expression node
  rw [expression_shape]
  apply if_returns program bindings state state state _ (boolean true) _ _ answer
  · apply native_binary_call_returns program bindings state state state state "<" (natural 0) (.var "fuel")
      (natural 0) (natural (fuel + 1)) (boolean true)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact grounded_returns program bindings state (.int 0)
    · exact variable_returns program bindings state "fuel"
    · simp [StdLib.less_comparison, natural, boolean]
  · simp only [boolean]
    rw [expression_else_shape]
    apply case_returns program bindings bound state state state (.var "codes")
      (.expression (MMBExecution.commandValue 50 index start after :: rest)) opcodeBody _ _
      expressionCases (read_cases_encoded expressionCases)
    · exact variable_returns program bindings state "codes"
    · simp [expression_cases_shape, MMBExecution.commandValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, referenceEnvironment, expressionEnvironment]
    · rw [opcode_shape]
      apply case_returns program bound bound state state state (.var "opcode") (natural 50) referenceBody _ _
        opcodeCases (read_cases_encoded opcodeCases)
      · exact variable_returns program bound state "opcode"
      · simp [opcode_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, natural]
      · exact body

private theorem expression_from_body (bindings : Subst) (state : State) (fuel pointer : Nat)
    (slots codes : List Atom) (images context resolver expression node answer : Atom)
    (fuelName matchingName codesName targetName : String)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural fuel)
    (matchingCaptured : applySubst bindings (.var matchingName) = matchingValue slots images context resolver)
    (codesCaptured : applySubst bindings (.var codesName) = listValue codes)
    (targetCaptured : applySubst bindings (.var targetName) = expressionValue pointer expression node)
    (body : PureReturns program (expressionEnvironment fuel pointer slots codes images context resolver expression node)
      state expressionEquation.body state answer) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:match-expression", .var fuelName, .var matchingName,
      .var codesName, .var targetName]) state answer := by
  apply authored_variable_call_returns program bindings
    (expressionEnvironment fuel pointer slots codes images context resolver expression node) state state "mm0:mmb:match-expression"
    [fuelName, matchingName, codesName, targetName] expressionEquation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _ body (by decide)
  simpa [fuelCaptured, matchingCaptured, codesCaptured, targetCaptured] using
    expression_clause fuel pointer slots codes images context resolver expression node

private theorem reference_filled_body_returns (state : State) (fuel pointer index start after stored : Nat)
    (slots rest : List Atom) (images context resolver expression node value shape : Atom)
    (found : slots[index]? = some (optionValue (some (expressionValue stored value shape)))) :
    PureReturns program (referenceEnvironment fuel pointer index start after slots rest images context resolver expression node)
      state referenceBody state (if stored = pointer then matchedValue slots images context resolver rest else .symbol "None") := by
  let bindings := referenceEnvironment fuel pointer index start after slots rest images context resolver expression node
  let bound := ("shape", shape) :: ("value", value) :: ("stored", natural stored) :: bindings
  rw [reference_shape]
  apply case_returns program bindings bound state state state _
    (optionValue (some (optionValue (some (expressionValue stored value shape))))) referenceFound _ _
    referenceCases (read_cases_encoded referenceCases)
  · simpa only [found] using reference_read_returns state fuel pointer index start after slots rest images context resolver expression node
  · simp [reference_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bound, bindings, referenceEnvironment,
      expressionEnvironment, optionValue, expressionValue]
  · rw [reference_found_shape]
    apply if_returns program bound state state state _ (boolean (stored == pointer)) _ _ _
    · apply native_binary_call_returns program bound state state state state "==" (.var "stored") (.var "pointer")
        (natural stored) (natural pointer) (boolean (stored == pointer))
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
      · exact variable_returns program bound state "stored"
      · exact variable_returns program bound state "pointer"
      · simp [StdLib.structural_equality, natural, boolean]
    · by_cases same : stored = pointer
      · simpa [boolean, same, bound, bindings] using
          reference_true_returns state fuel pointer index start after stored slots rest images context resolver expression node value shape
      · simpa [boolean, same] using symbol_returns program bound state "None"

/-- A reference checks the source allocation identity. The formula and node
payloads may differ; conversely, equal payloads cannot justify unequal IDs. -/
theorem match_reference_returns (bindings : Subst) (state : State) (fuel pointer index start after stored : Nat)
    (slots rest : List Atom) (images context resolver expression node value shape : Atom)
    (fuelName matchingName codesName targetName : String)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 1))
    (matchingCaptured : applySubst bindings (.var matchingName) = matchingValue slots images context resolver)
    (codesCaptured : applySubst bindings (.var codesName) = listValue (MMBExecution.commandValue 50 index start after :: rest))
    (targetCaptured : applySubst bindings (.var targetName) = expressionValue pointer expression node)
    (found : slots[index]? = some (optionValue (some (expressionValue stored value shape)))) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:match-expression", .var fuelName, .var matchingName,
      .var codesName, .var targetName]) state
      (if stored = pointer then matchedValue slots images context resolver rest else .symbol "None") := by
  exact expression_from_body bindings state (fuel + 1) pointer slots
    (MMBExecution.commandValue 50 index start after :: rest) images context resolver expression node _
    fuelName matchingName codesName targetName fuelCaptured matchingCaptured codesCaptured targetCaptured
    (expression_reference_from_body state fuel pointer index start after slots rest images context resolver expression node _
      (reference_filled_body_returns state fuel pointer index start after stored slots rest images context resolver expression node value shape found))

private theorem reference_unavailable_body_returns (state : State) (fuel pointer index start after : Nat)
    (slots rest : List Atom) (images context resolver expression node : Atom)
    (unavailable : slots[index]? = none ∨ slots[index]? = some (.symbol "None")) :
    PureReturns program (referenceEnvironment fuel pointer index start after slots rest images context resolver expression node)
      state referenceBody state (.symbol "None") := by
  let bindings := referenceEnvironment fuel pointer index start after slots rest images context resolver expression node
  let bad := ("bad", optionValue (slots[index]?)) :: bindings
  rw [reference_shape]
  apply case_returns program bindings bad state state state _ (optionValue (slots[index]?)) (.symbol "None") _ _
    referenceCases (read_cases_encoded referenceCases)
  · exact reference_read_returns state fuel pointer index start after slots rest images context resolver expression node
  · rcases unavailable with unavailable | unavailable <;>
      simp [reference_cases_shape, unavailable, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings, bad, referenceEnvironment,
        expressionEnvironment, optionValue]
  · exact symbol_returns program bad state "None"

/-- An unavailable or merely reserved slot is explicitly refused by the
original reference instruction; reservation alone grants no pointer access. -/
theorem match_reference_unavailable_returns (bindings : Subst) (state : State) (fuel pointer index start after : Nat)
    (slots rest : List Atom) (images context resolver expression node : Atom)
    (fuelName matchingName codesName targetName : String)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural (fuel + 1))
    (matchingCaptured : applySubst bindings (.var matchingName) = matchingValue slots images context resolver)
    (codesCaptured : applySubst bindings (.var codesName) = listValue (MMBExecution.commandValue 50 index start after :: rest))
    (targetCaptured : applySubst bindings (.var targetName) = expressionValue pointer expression node)
    (unavailable : slots[index]? = none ∨ slots[index]? = some (.symbol "None")) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:match-expression", .var fuelName, .var matchingName,
      .var codesName, .var targetName]) state (.symbol "None") :=
  expression_from_body bindings state (fuel + 1) pointer slots
    (MMBExecution.commandValue 50 index start after :: rest) images context resolver expression node _
    fuelName matchingName codesName targetName fuelCaptured matchingCaptured codesCaptured targetCaptured
    (expression_reference_from_body state fuel pointer index start after slots rest images context resolver expression node _
      (reference_unavailable_body_returns state fuel pointer index start after slots rest images context resolver expression node unavailable))

/-- The source's explicit matching-fuel refusal occurs before any command or
slot inspection and leaves all matching and execution state untouched. -/
theorem match_zero_fuel_returns (bindings : Subst) (state : State) (pointer : Nat)
    (slots codes : List Atom) (images context resolver expression node : Atom)
    (fuelName matchingName codesName targetName : String)
    (fuelCaptured : applySubst bindings (.var fuelName) = natural 0)
    (matchingCaptured : applySubst bindings (.var matchingName) = matchingValue slots images context resolver)
    (codesCaptured : applySubst bindings (.var codesName) = listValue codes)
    (targetCaptured : applySubst bindings (.var targetName) = expressionValue pointer expression node) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:match-expression", .var fuelName, .var matchingName,
      .var codesName, .var targetName]) state (.symbol "None") := by
  apply expression_from_body bindings state 0 pointer slots codes images context resolver expression node _
    fuelName matchingName codesName targetName fuelCaptured matchingCaptured codesCaptured targetCaptured
  let inner := expressionEnvironment 0 pointer slots codes images context resolver expression node
  rw [expression_shape]
  apply if_returns program inner state state state _ (boolean false) _ _ _
  · apply native_binary_call_returns program inner state state state state "<" (natural 0) (.var "fuel")
      (natural 0) (natural 0) (boolean false)
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact grounded_returns program inner state (.int 0)
    · exact variable_returns program inner state "fuel"
    · simp [StdLib.less_comparison, natural, boolean]
  · simpa [boolean] using symbol_returns program inner state "None"

end Mettapedia.Languages.MM0.MeTTa.MMBAssertionMatchExecution
