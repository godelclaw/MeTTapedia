import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MatchAuthority

/-!
# Original complete assertion theorem matching

The unchanged quoted source prepares physical slots, computes its code-derived
fuel, matches the conclusion and then traverses the reversed supplied hypothesis
sequence. These laws cover successful finite composition and completed Boolean
refusal. Accepted slots preserve the complete chronological allocation evidence,
including occurrence order, duplicates and newly reserved entries.

This module does not validate proof witnesses. Logical authorization remains
with the original kernel and chronological saved-proof service. Whole theorem
application and conversion dispatch are separate source-execution joins.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

namespace Mettapedia.Languages.MM0.MeTTa.MMBTheoremMatchExecution
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (expressionValue)
open MMBAssertionMatchExecution (matchingValue matchedValue initialSlots)
open MMBRecursiveMatchExecution
open MMBAllocationExecution
open MMBMatchAuthority
abbrev program := MMBRecursiveMatchExecution.program

/-- The unchanged authored theorem matcher derives its fuel from code count. -/
def matchFuel (codes : List Atom) : Nat := 2 * codes.length + 2

def theoremValue (arguments : Atom) (codes : List Atom) (endPosition : Atom) : Atom :=
  .expression [.symbol "MM0:MMBTheorem", arguments,
    .expression [.symbol "MM0:MMBStream", listValue codes, endPosition]]

def callBindings (resolver context declaration arguments hypotheses target : Atom) : Subst :=
  [("target", target), ("hypotheses", hypotheses), ("arguments", arguments),
   ("declaration", declaration), ("context", context), ("resolver", resolver)]
def callExpression : Atom := .expression [.symbol "mm0:mmb:match-theorem", .var "resolver", .var "context",
  .var "declaration", .var "arguments", .var "hypotheses", .var "target"]

/-- Exact original assertion matching followed by its reversed hypothesis
sequence. Refusal of either source phase is an explicit false result. -/
inductive Match (context resolver : Atom) (arguments codes hypotheses : List Atom) (target : Atom) :
    Option (List Atom) → Prop
  | expressionRefused
      (matched : ExpressionMatch (listValue []) context resolver (matchFuel codes)
        (initialSlots arguments) codes target none) : Match context resolver arguments codes hypotheses target none
  | hypotheses (middle unread : List Atom) (result : Option (List Atom))
      (matched : ExpressionMatch (listValue []) context resolver (matchFuel codes)
        (initialSlots arguments) codes target (some (middle, unread)))
      (continued : HypothesisMatch (listValue []) context resolver (matchFuel codes)
        middle unread hypotheses.reverse result) : Match context resolver arguments codes hypotheses target result

private def sourceEquation : SpaceSemantics.Equation :=
  ((MMBExecution.binarySource.program.equations.filter (·.head == "mm0:mmb:match-theorem")).head?).getD
    ⟨"", [], .symbol "None"⟩
private def environment (resolver context declarationArguments endPosition : Atom)
    (arguments codes hypotheses : List Atom) (target : Atom) : Subst :=
  [("target",target), ("hypotheses",listValue hypotheses), ("arguments",listValue arguments),
   ("end",endPosition), ("codes",.expression codes), ("args",declarationArguments),
   ("context",context), ("resolver",resolver)]
private def guardCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "MM0:MMBExpression",.var "id",.var "value",.var "node"],boolean true),
   (.var "bad",boolean false)]
private def guard : Atom := .expression [.symbol "case",.var "target",
  .expression (guardCases.map fun row => .expression [row.1,row.2])]
private def resultCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some",.var "final"],boolean true),(.var "bad",boolean false)]
private def finalCase : Atom := .expression [.symbol "case",
  .expression [.symbol "mm0:mmb:match-hypotheses",.var "fuel",.var "after",.var "rest",
    .expression [.symbol "MM0:L",.var "ordered"]],
  .expression (resultCases.map fun row => .expression [row.1,row.2])]
private def reversedCase : Atom := .expression [.symbol "let",.var "ordered",
  .expression [.symbol "reverse",.var "hyps"],finalCase]
private def hypothesisCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "MM0:L",.var "hyps"],reversedCase),(.var "bad",boolean false)]
private def hypothesisCase : Atom := .expression [.symbol "case",.var "hypotheses",
  .expression (hypothesisCases.map fun row => .expression [row.1,row.2])]
private def matchedCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some",.expression [.symbol "MM0:MMBMatched",.var "after",.var "rest"]],hypothesisCase),
   (.var "bad",boolean false)]
private def matchedCase : Atom := .expression [.symbol "case",
  .expression [.symbol "mm0:mmb:match-expression",.var "fuel",.var "matching",
    .expression [.symbol "MM0:L",.var "codes"],.var "target"],
  .expression (matchedCases.map fun row => .expression [row.1,row.2])]
private def fuelExpression : Atom := .expression [.symbol "+",
  .expression [.symbol "*",natural 2,.expression [.symbol "size-atom",.var "codes"]],natural 2]
private def pairs : List Atom :=
  [.expression [.var "slots",.expression [.symbol "mm0:mmb:match-slots",.var "arguments"]],
   .expression [.var "matching",.expression [.symbol "MM0:MMBMState",.var "slots",
     .expression [.symbol "MM0:L",.expression []],.var "context",.var "resolver",.symbol "MM0:MMBAssertionMatch"]],
   .expression [.var "fuel",fuelExpression]]
private def successBody : Atom := .expression [.symbol "let*",.expression pairs,matchedCase]
private theorem source_unique : program.equations.filter (·.head == "mm0:mmb:match-theorem") = [sourceEquation] := by decide +kernel
private theorem source_shape : sourceEquation.body = .expression [.symbol "if",guard,successBody,boolean false] := by decide
private theorem source_formals : sourceEquation.arguments =
  [.var "resolver",.var "context",.expression [.symbol "MM0:MMBTheorem",.var "args",
    .expression [.symbol "MM0:MMBStream",.expression [.symbol "MM0:L",.var "codes"],.var "end"]],
   .var "arguments",.var "hypotheses",.var "target"] := by decide
private theorem source_clause (resolver context declarationArguments endPosition : Atom)
    (arguments codes hypotheses : List Atom) (target : Atom) :
    clauses program "mm0:mmb:match-theorem"
      [resolver,context,theoremValue declarationArguments codes endPosition,listValue arguments,listValue hypotheses,target] =
      [.evaluate (environment resolver context declarationArguments endPosition arguments codes hypotheses target) sourceEquation.body] := by
  rw [clauses_use_only_the_named_equations,source_unique]
  simp [source_formals,theoremValue,environment,listValue,SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup]

private theorem passive_variables (names : List String) (head : String) :
    ∀ offset argument, (names.map Atom.var)[offset]? = some argument →
      argumentIsRaw program head offset = true ∨ passiveArgument argument = true := by
  intro offset argument found
  simp only [List.getElem?_map] at found
  cases selected : names[offset]? with
  | none => simp [selected] at found
  | some name => simp [selected] at found; subst argument; exact .inr rfl

private theorem fuel_returns (state : State) (bindings : Subst) (codes : List Atom)
    (captured : applySubst bindings (.var "codes") = .expression codes) :
    PureReturns program bindings state fuelExpression state (natural (matchFuel codes)) := by
  unfold fuelExpression
  apply native_binary_call_returns program bindings state state state state "+" _ (natural 2)
    (natural (2*codes.length)) (natural 2) _
    (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
  · apply native_binary_call_returns program bindings state state state state "*" (natural 2) _
      (natural 2) (natural codes.length) (natural (2*codes.length))
      (by decide) (by decide) (by decide +kernel) (by decide +kernel) _ _ _ (by decide)
    · exact grounded_returns program bindings state (.int 2)
    · apply native_unary_call_returns program bindings state state state "size-atom" (.var "codes")
        (.expression codes) (natural codes.length) (by decide) (by decide) (by decide +kernel) _ _ (by decide)
      · simpa [captured] using variable_returns program bindings state "codes"
      · simp [natural]
    · simp [natural]
  · exact grounded_returns program bindings state (.int 2)
  · simp [natural,matchFuel]

private theorem hypothesis_body_returns (state : State) (bindings : Subst)
    (context resolver : Atom) (fuel : Nat) (middle unread hypotheses : List Atom) (result : Option (List Atom))
    (fuelCaptured : applySubst bindings (.var "fuel") = natural fuel)
    (afterCaptured : applySubst bindings (.var "after") = matchingValue middle (listValue []) context resolver)
    (restCaptured : applySubst bindings (.var "rest") = listValue unread)
    (hypothesesCaptured : applySubst bindings (.var "hypotheses") = listValue hypotheses)
    (fresh : ∀ name ∈ ["hyps","ordered","final","bad"], Subst.lookup bindings name = none)
    (trace : HypothesisMatch (listValue []) context resolver fuel middle unread hypotheses.reverse result) :
    PureReturns program bindings state hypothesisCase state (boolean result.isSome) := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  simp only [applySubst,Subst.lookup] at fuelCaptured afterCaptured restCaptured hypothesesCaptured
  let bound := ("hyps",.expression hypotheses)::bindings
  let ordered := ("ordered",.expression hypotheses.reverse)::bound
  unfold hypothesisCase
  apply case_returns program bindings bound state state state (.var "hypotheses") (listValue hypotheses)
    reversedCase _ _ hypothesisCases (read_cases_encoded hypothesisCases)
  · simpa [applySubst,Subst.lookup,hypothesesCaptured] using variable_returns program bindings state "hypotheses"
  · simp [hypothesisCases,listValue,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,bound,freshLookup]
  · unfold reversedCase
    apply let_returns program bound ordered state state state (.var "ordered") _ finalCase
      (.expression hypotheses.reverse) _
    · apply native_unary_call_returns program bound state state state "reverse" (.var "hyps")
        (.expression hypotheses) (.expression hypotheses.reverse) (by decide) (by decide) (by decide +kernel) _ _ (by decide)
      · exact variable_returns program bound state "hyps"
      · exact StdLib.reverse_returns_expression state hypotheses
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,ordered,bound,freshLookup]
    · unfold finalCase
      have returned := hypotheses_returns state (listValue []) context resolver fuel middle unread hypotheses.reverse result trace
      have stage := captured_function_arguments_returns program
        (MMBRecursiveMatchExecution.callBindings fuel (matchingValue middle (listValue []) context resolver)
          (listValue unread) (listValue hypotheses.reverse)) ordered state state "mm0:mmb:match-hypotheses"
        (["fuel","matching","codes","target"].map Atom.var) 4 (hypothesisValue (listValue []) context resolver result)
        (by decide +kernel) (by decide) (passive_variables _ _) returned
      have sourceCall : PureReturns program ordered state
          (.expression [.symbol "mm0:mmb:match-hypotheses",.var "fuel",.var "after",.var "rest",
            .expression [.symbol "MM0:L",.var "ordered"]]) state
          (hypothesisValue (listValue []) context resolver result) := by
        apply call_returns program ordered state state "mm0:mmb:match-hypotheses" _ _ (by decide +kernel) _ (by decide)
        apply evaluated_argument_returns program ordered state state state (.function "mm0:mmb:match-hypotheses")
          (.var "fuel") (natural fuel) _ _ [] 0 (by decide +kernel)
          (by simpa [ordered,bound,applySubst,Subst.lookup,fuelCaptured] using variable_returns program ordered state "fuel")
        apply raw_arguments_return program ordered state state "mm0:mmb:match-hypotheses"
          [.var "after",.var "rest",.expression [.symbol "MM0:L",.var "ordered"]] [natural fuel] 1 _
          (by
            intro offset bounded
            have bound : offset < 3 := by simpa using bounded
            interval_cases offset <;> decide +kernel)
        simpa [MMBRecursiveMatchExecution.callBindings,applySubst,applySubst.applySubstList,Subst.lookup,
          ordered,bound,fuelCaptured,afterCaptured,restCaptured,listValue] using stage
      cases result with
      | none =>
          let failed := ("bad",.symbol "None")::ordered
          apply case_returns program ordered failed state state state _ (.symbol "None") (boolean false) _ _
            resultCases (read_cases_encoded resultCases)
          · simpa [hypothesisValue,optionValue] using sourceCall
          · simp [resultCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,Subst.lookup,failed,ordered,bound,freshLookup]
          · exact grounded_returns program failed state (.bool false)
      | some final =>
          let finished := ("final",matchingValue final (listValue []) context resolver)::ordered
          apply case_returns program ordered finished state state state _
            (optionValue (some (matchingValue final (listValue []) context resolver))) (boolean true) _ _
            resultCases (read_cases_encoded resultCases)
          · simpa [hypothesisValue,optionValue] using sourceCall
          · simp [resultCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,finished,optionValue,ordered,bound,freshLookup]
          · exact grounded_returns program finished state (.bool true)


private theorem matching_returns (state : State) (bindings : Subst) (slots : List Atom) (context resolver : Atom)
    (slotsCaptured : applySubst bindings (.var "slots") = listValue slots)
    (contextCaptured : applySubst bindings (.var "context") = context)
    (resolverCaptured : applySubst bindings (.var "resolver") = resolver) :
    PureReturns program bindings state
      (.expression [.symbol "MM0:MMBMState",.var "slots",.expression [.symbol "MM0:L",.expression []],
        .var "context",.var "resolver",.symbol "MM0:MMBAssertionMatch"]) state
      (matchingValue slots (listValue []) context resolver) := by
  apply data_call_returns program bindings state state "MM0:MMBMState" _ _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings state state state .data
    (.symbol "MM0:MMBMState") (.symbol "MM0:MMBMState") _ _ [] 0 rfl
    (symbol_returns program bindings state "MM0:MMBMState")
  apply evaluated_argument_returns program bindings state state state .data (.var "slots") (listValue slots) _ _ _ 1 rfl
    (by simpa [slotsCaptured] using variable_returns program bindings state "slots")
  apply evaluated_argument_returns program bindings state state state .data _ (listValue []) _ _ _ 2 rfl
    (empty_constructor_returns program bindings state "MM0:L" (by decide +kernel) (by decide))
  apply evaluated_argument_returns program bindings state state state .data (.var "context") context _ _ _ 3 rfl
    (by simpa [contextCaptured] using variable_returns program bindings state "context")
  apply evaluated_argument_returns program bindings state state state .data (.var "resolver") resolver _ _ _ 4 rfl
    (by simpa [resolverCaptured] using variable_returns program bindings state "resolver")
  apply evaluated_argument_returns program bindings state state state .data
    (.symbol "MM0:MMBAssertionMatch") (.symbol "MM0:MMBAssertionMatch") _ [] _ 5 rfl
    (symbol_returns program bindings state "MM0:MMBAssertionMatch")
  exact data_arguments_values_return program bindings state _ 6

private theorem matched_body_returns (state : State) (bindings : Subst)
    (context resolver : Atom) (arguments codes hypotheses : List Atom) (target : Atom) (result : Option (List Atom))
    (fuelCaptured : applySubst bindings (.var "fuel") = natural (matchFuel codes))
    (matchingCaptured : applySubst bindings (.var "matching") = matchingValue (initialSlots arguments) (listValue []) context resolver)
    (codesCaptured : applySubst bindings (.var "codes") = .expression codes)
    (targetCaptured : applySubst bindings (.var "target") = target)
    (hypothesesCaptured : applySubst bindings (.var "hypotheses") = listValue hypotheses)
    (fresh : ∀ name ∈ ["rest","after","hyps","ordered","final","bad"], Subst.lookup bindings name = none)
    (trace : Match context resolver arguments codes hypotheses target result) :
    PureReturns program bindings state matchedCase state (boolean result.isSome) := by
  have freshLookup := fresh
  simp only [Subst.lookup] at freshLookup
  simp only [applySubst,Subst.lookup] at fuelCaptured matchingCaptured codesCaptured targetCaptured hypothesesCaptured
  unfold matchedCase
  cases trace with
  | expressionRefused matched =>
    have returned := expression_returns state (listValue []) context resolver (matchFuel codes)
      (initialSlots arguments) codes target none matched
    have stage := captured_function_arguments_returns program
      (MMBRecursiveMatchExecution.callBindings (matchFuel codes)
        (matchingValue (initialSlots arguments) (listValue []) context resolver) (listValue codes) target)
      bindings state state "mm0:mmb:match-expression" (["fuel","matching","codes","target"].map Atom.var) 4
      (.symbol "None") (by decide +kernel) (by decide) (passive_variables _ _) returned
    have called : PureReturns program bindings state
        (.expression [.symbol "mm0:mmb:match-expression",.var "fuel",.var "matching",
          .expression [.symbol "MM0:L",.var "codes"],.var "target"]) state (.symbol "None") := by
      apply call_returns program bindings state state "mm0:mmb:match-expression" _ _ (by decide +kernel) _ (by decide)
      apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:match-expression")
        (.var "fuel") (natural (matchFuel codes)) _ _ [] 0 (by decide +kernel)
        (by simpa [applySubst,Subst.lookup,fuelCaptured] using variable_returns program bindings state "fuel")
      apply raw_arguments_return program bindings state state "mm0:mmb:match-expression"
        [.var "matching",.expression [.symbol "MM0:L",.var "codes"],.var "target"] [natural (matchFuel codes)] 1 _
        (by
            intro offset bounded
            have bound : offset < 3 := by simpa using bounded
            interval_cases offset <;> decide +kernel)
      simpa [MMBRecursiveMatchExecution.callBindings,applySubst,applySubst.applySubstList,Subst.lookup,
        fuelCaptured,matchingCaptured,codesCaptured,targetCaptured,listValue] using stage
    let failed := ("bad",.symbol "None")::bindings
    apply case_returns program bindings failed state state state _ (.symbol "None") (boolean false) _ _
      matchedCases (read_cases_encoded matchedCases) called
    · simp [matchedCases,SpaceSemantics.selectCase,SpaceSemantics.matchValue,matchAtom,Subst.lookup,failed,freshLookup]
    · exact grounded_returns program failed state (.bool false)
  | hypotheses middle unread result matched continued =>
    have returned := expression_returns state (listValue []) context resolver (matchFuel codes)
      (initialSlots arguments) codes target (some (middle,unread)) matched
    have stage := captured_function_arguments_returns program
      (MMBRecursiveMatchExecution.callBindings (matchFuel codes)
        (matchingValue (initialSlots arguments) (listValue []) context resolver) (listValue codes) target)
      bindings state state "mm0:mmb:match-expression" (["fuel","matching","codes","target"].map Atom.var) 4
      (matchedValue middle (listValue []) context resolver unread)
      (by decide +kernel) (by decide) (passive_variables _ _) returned
    have called : PureReturns program bindings state
        (.expression [.symbol "mm0:mmb:match-expression",.var "fuel",.var "matching",
          .expression [.symbol "MM0:L",.var "codes"],.var "target"]) state
        (matchedValue middle (listValue []) context resolver unread) := by
      apply call_returns program bindings state state "mm0:mmb:match-expression" _ _ (by decide +kernel) _ (by decide)
      apply evaluated_argument_returns program bindings state state state (.function "mm0:mmb:match-expression")
        (.var "fuel") (natural (matchFuel codes)) _ _ [] 0 (by decide +kernel)
        (by simpa [applySubst,Subst.lookup,fuelCaptured] using variable_returns program bindings state "fuel")
      apply raw_arguments_return program bindings state state "mm0:mmb:match-expression"
        [.var "matching",.expression [.symbol "MM0:L",.var "codes"],.var "target"] [natural (matchFuel codes)] 1 _
        (by
            intro offset bounded
            have bound : offset < 3 := by simpa using bounded
            interval_cases offset <;> decide +kernel)
      simpa [MMBRecursiveMatchExecution.callBindings,applySubst,applySubst.applySubstList,Subst.lookup,
        fuelCaptured,matchingCaptured,codesCaptured,targetCaptured,listValue] using stage
    let next := ("rest",listValue unread)::("after",matchingValue middle (listValue []) context resolver)::bindings
    apply case_returns program bindings next state state state _
      (matchedValue middle (listValue []) context resolver unread) hypothesisCase _ _
      matchedCases (read_cases_encoded matchedCases) called
    · simp [matchedCases,matchedValue,optionValue,SpaceSemantics.selectCase,SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,next,freshLookup]
    · apply hypothesis_body_returns state next context resolver (matchFuel codes) middle unread hypotheses result
      · simpa [next,applySubst,Subst.lookup] using fuelCaptured
      · simp [next,applySubst,Subst.lookup]
      · simp [next,applySubst,Subst.lookup]
      · simpa [next,applySubst,Subst.lookup] using hypothesesCaptured
      · intro name member
        simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
        rcases member with rfl|rfl|rfl|rfl <;> simpa [next,Subst.lookup] using fresh _ (by simp)
      · exact continued

private theorem success_body_returns (state : State) (resolver context declarationArguments endPosition : Atom)
    (arguments codes hypotheses : List Atom) (target : Atom) (result : Option (List Atom))
    (trace : Match context resolver arguments codes hypotheses target result) :
    PureReturns program (environment resolver context declarationArguments endPosition arguments codes hypotheses target)
      state successBody state (boolean result.isSome) := by
  let bindings := environment resolver context declarationArguments endPosition arguments codes hypotheses target
  let slotted := ("slots",listValue (initialSlots arguments))::bindings
  let initialized := ("matching",matchingValue (initialSlots arguments) (listValue []) context resolver)::slotted
  let fueled := ("fuel",natural (matchFuel codes))::initialized
  let matchingExpression := (.expression [.symbol "MM0:MMBMState",.var "slots",.expression [.symbol "MM0:L",.expression []],
    .var "context",.var "resolver",.symbol "MM0:MMBAssertionMatch"] : Atom)
  let nested := (.expression [.symbol "let",.var "slots",.expression [.symbol "mm0:mmb:match-slots",.var "arguments"],
    .expression [.symbol "let",.var "matching",matchingExpression,
      .expression [.symbol "let",.var "fuel",fuelExpression,matchedCase]]] : Atom)
  unfold successBody
  apply let_star_returns program bindings state state pairs matchedCase nested _ (by rfl)
  apply let_returns program bindings slotted state state state (.var "slots") _ _ (listValue (initialSlots arguments)) _
  · exact MMBAssertionMatchExecution.match_slots_returns bindings state arguments (.var "arguments") rfl
  · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,slotted,bindings,environment]
  · apply let_returns program slotted initialized state state state (.var "matching") matchingExpression _
      (matchingValue (initialSlots arguments) (listValue []) context resolver) _
    · exact matching_returns state slotted (initialSlots arguments) context resolver rfl rfl rfl
    · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,initialized,slotted,bindings,environment]
    · apply let_returns program initialized fueled state state state (.var "fuel") fuelExpression matchedCase
        (natural (matchFuel codes)) _
      · exact fuel_returns state initialized codes rfl
      · simp [SpaceSemantics.matchBinding,SpaceSemantics.matchValue,matchAtom,Subst.lookup,fueled,initialized,slotted,bindings,environment]
      · exact matched_body_returns state fueled context resolver arguments codes hypotheses target result rfl rfl rfl rfl rfl
          (by intro name member; simp only [List.mem_cons,List.mem_nil_iff,or_false] at member;
              rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl) trace

/-- The complete unchanged theorem wrapper executes both original recursive
phases, including code-derived fuel and source hypothesis reversal. -/
theorem returns (state : State) (resolver context declarationArguments endPosition : Atom)
    (arguments codes hypotheses : List Atom) (pointer : Nat) (value node : Atom) (result : Option (List Atom))
    (trace : Match context resolver arguments codes hypotheses (expressionValue pointer value node) result) :
    PureReturns program
      (callBindings resolver context (theoremValue declarationArguments codes endPosition)
        (listValue arguments) (listValue hypotheses) (expressionValue pointer value node)) state callExpression state
      (boolean result.isSome) := by
  let target := expressionValue pointer value node
  let bindings := environment resolver context declarationArguments endPosition arguments codes hypotheses target
  have body : PureReturns program bindings state sourceEquation.body state (boolean result.isSome) := by
    rw [source_shape]
    apply if_returns program bindings state state state guard (boolean true) successBody (boolean false) _
    · unfold guard
      let captured := ("node",node)::("value",value)::("id",natural pointer)::bindings
      apply case_returns program bindings captured state state state (.var "target") target (boolean true) _ _
        guardCases (read_cases_encoded guardCases)
      · exact variable_returns program bindings state "target"
      · simp [guardCases,target,expressionValue,bindings,environment,SpaceSemantics.selectCase,
          SpaceSemantics.matchValue,SpaceSemantics.matchValue.matchValues,matchAtom,Subst.lookup,captured]
      · exact grounded_returns program captured state (.bool true)
    · simpa [boolean] using success_body_returns state resolver context declarationArguments endPosition arguments codes hypotheses target result trace
  apply authored_variable_call_returns program _ bindings state state "mm0:mmb:match-theorem"
    ["resolver","context","declaration","arguments","hypotheses","target"] sourceEquation.body _
    (by decide) (by decide) (by decide +kernel) _ body (by decide)
  simpa [callBindings,applySubst,Subst.lookup] using
    source_clause resolver context declarationArguments endPosition arguments codes hypotheses target

private theorem hypotheses_slots_prefix (images context resolver : Atom) (fuel : Nat)
    (slots codes targets final : List Atom)
    (trace : HypothesisMatch images context resolver fuel slots codes targets (some final)) :
    ∃ fresh, final = slots ++ fresh := by
  induction fuel generalizing slots codes targets final with
  | zero =>
    cases trace with
    | empty => exact ⟨[],by simp⟩
  | succ fuel ih =>
    cases trace with
    | empty => exact ⟨[],by simp⟩
    | next _ data start next slots codes middle unread first earlier _ matched continued =>
      obtain ⟨headFresh,headSame⟩ := ExpressionMatch.preserves_slots images context resolver fuel
        _ _ _ _ _ matched
      obtain ⟨tailFresh,tailSame⟩ := ih _ _ _ _ continued
      exact ⟨headFresh++tailFresh,by rw [tailSame,headSame,List.append_assoc]⟩

/-- Matching extends only the physical slot suffix. Supplied slots and their
complete original pointers remain in authored order. -/
theorem Match.preserves_slots {context resolver : Atom} {arguments codes hypotheses : List Atom} {target : Atom}
    {final : List Atom} (trace : Match context resolver arguments codes hypotheses target (some final)) :
    ∃ fresh, final = initialSlots arguments ++ fresh := by
  cases trace with
  | hypotheses middle unread _ matched continued =>
    obtain ⟨firstFresh,firstSame⟩ := ExpressionMatch.preserves_slots (listValue []) context resolver
      (matchFuel codes) _ _ _ _ _ matched
    obtain ⟨restFresh,restSame⟩ := hypotheses_slots_prefix (listValue []) context resolver
      (matchFuel codes) _ _ _ _ continued
    exact ⟨firstFresh++restFresh,by rw [restSame,firstSame,List.append_assoc]⟩

/-- Slot authority is earned from the original chronological expression
history, not from equality of an untrusted target payload. -/
theorem Match.authorized_slots {history : List Atom} (built : ConstructedHistory history)
    {context resolver : Atom} {arguments codes hypotheses : List Atom} {target : Atom} {final : List Atom}
    (trace : Match context resolver arguments codes hypotheses target (some final))
    (argumentsAuthorized : ∀ argument ∈ arguments, AuthorizedExpression history argument)
    (targetAuthorized : AuthorizedExpression history target)
    (hypothesesAuthorized : ∀ target ∈ hypotheses, AuthorizedExpression history target) :
    SlotsAuthorized history final := by
  cases trace with
  | hypotheses middle unread _ matched continued =>
    have initialized := SlotsAuthorized.initial argumentsAuthorized
    have after := expression_authorized_slots built (listValue []) context resolver (matchFuel codes)
      _ _ _ _ _ matched initialized targetAuthorized
    exact hypotheses_authorized_slots built (listValue []) context resolver (matchFuel codes)
      _ _ _ _ continued after (by simpa using hypothesesAuthorized)

/-- Every admitted original wrapper terminates with either acceptance or its
actual refusal; each accepted slot retains chronological allocation authority. -/
theorem total {history : List Atom} (built : ConstructedHistory history)
    (context resolver : Atom) (arguments codes hypotheses : List Atom) (target : Atom)
    (argumentsAuthorized : ∀ argument ∈ arguments, AuthorizedExpression history argument)
    (targetAuthorized : AuthorizedExpression history target)
    (hypothesesAuthorized : ∀ target ∈ hypotheses, AuthorizedExpression history target)
    (codesShape : CodesWellFormed codes) :
    ∃ result, Match context resolver arguments codes hypotheses target result ∧
      ∀ final, result = some final → SlotsAuthorized history final := by
  have initialized := SlotsAuthorized.initial argumentsAuthorized
  obtain ⟨first,matched,shape⟩ := expression_total [] context resolver (matchFuel codes)
    (initialSlots arguments) codes target initialized.wellFormed codesShape (targetAuthorized.shape built)
  cases first with
  | none => exact ⟨none,.expressionRefused matched,by simp⟩
  | some pair =>
    obtain ⟨middle,unread⟩ := pair
    obtain ⟨slotsShape,restShape⟩ := shape _ _ rfl
    obtain ⟨result,continued,_⟩ := hypotheses_total [] context resolver (matchFuel codes) middle unread hypotheses.reverse
      slotsShape restShape (by intro target member; exact (hypothesesAuthorized target (by simpa using member)).shape built)
    have trace : Match context resolver arguments codes hypotheses target result := .hypotheses middle unread result matched continued
    exact ⟨result,trace,by intro final accepted; cases accepted; exact trace.authorized_slots built argumentsAuthorized targetAuthorized hypothesesAuthorized⟩


/-- A filled accepted slot retains a complete original kernel preterm;
original allocation identity remains part of the evidence. -/
theorem Match.filled_slots {history : List Atom} (built : ConstructedHistory history)
    {context resolver : Atom} {arguments codes hypotheses : List Atom} {target : Atom} {final : List Atom}
    (trace : Match context resolver arguments codes hypotheses target (some final))
    (argumentsAuthorized : ∀ argument ∈ arguments, AuthorizedExpression history argument)
    (targetAuthorized : AuthorizedExpression history target)
    (hypothesesAuthorized : ∀ target ∈ hypotheses, AuthorizedExpression history target)
    (index : Nat) (entry : Atom) (found : final[index]? = some (optionValue (some entry))) :
    ∃ pointer expression node, entry = expressionValue pointer (Data.preterm expression) node :=
  (trace.authorized_slots built argumentsAuthorized targetAuthorized hypothesesAuthorized).preterms built index entry found

/-- Completed source observations retain the whole state and have no input or
output side effects. False refusal is a completed Boolean observation. -/
theorem completed_iff (state : State) (resolver context declarationArguments endPosition : Atom)
    (arguments codes hypotheses : List Atom) (pointer : Nat) (value node : Atom) (result : Option (List Atom))
    (trace : Match context resolver arguments codes hypotheses (expressionValue pointer value node) result)
    (after : State) (answers input output : List Atom) :
    (∃ budget, run program budget {state := state, control := (.evaluate
      (callBindings resolver context (theoremValue declarationArguments codes endPosition)
        (listValue arguments) (listValue hypotheses) (expressionValue pointer value node)) callExpression)}
      = .complete after answers input output) ↔
      after = state ∧ answers = [boolean result.isSome] ∧ input = [] ∧ output = [] :=
  pure_returns_completed_iff program _ state state _ _
    (returns state resolver context declarationArguments endPosition arguments codes hypotheses pointer value node result trace)
    after answers input output

/-- On original admitted histories the wrapper accepts exactly an original
complete match trace. Source refusal and admission remain independent of kernel
proof validity, which is checked by the saved-proof service. -/
theorem accepted_iff_match {history : List Atom} (built : ConstructedHistory history)
    (state : State) (resolver context declarationArguments endPosition : Atom)
    (arguments codes hypotheses : List Atom) (pointer : Nat) (value node : Atom)
    (argumentsAuthorized : ∀ argument ∈ arguments, AuthorizedExpression history argument)
    (targetAuthorized : AuthorizedExpression history (expressionValue pointer value node))
    (hypothesesAuthorized : ∀ target ∈ hypotheses, AuthorizedExpression history target)
    (codesShape : CodesWellFormed codes) :
    (∃ budget, run program budget {state := state, control := (.evaluate
      (callBindings resolver context (theoremValue declarationArguments codes endPosition)
        (listValue arguments) (listValue hypotheses) (expressionValue pointer value node)) callExpression)}
      = .complete state [boolean true] [] []) ↔
      ∃ final, Match context resolver arguments codes hypotheses (expressionValue pointer value node) (some final) := by
  obtain ⟨result,trace,_⟩ := total built context resolver arguments codes hypotheses _
    argumentsAuthorized targetAuthorized hypothesesAuthorized codesShape
  constructor
  · intro completed
    have observation := (completed_iff state resolver context declarationArguments endPosition arguments codes hypotheses
      pointer value node result trace state [boolean true] [] []).mp completed
    cases result with
    | none => simp [boolean] at observation
    | some final => exact ⟨final,trace⟩
  · rintro ⟨final,matched⟩
    exact (completed_iff state resolver context declarationArguments endPosition arguments codes hypotheses
      pointer value node (some final) matched state [boolean true] [] []).mpr (by simp)

end Mettapedia.Languages.MM0.MeTTa.MMBTheoremMatchExecution
