import Mettapedia.Languages.HOLLight.MeTTa.ReceiptKeys
import Mettapedia.Languages.HOLLight.MeTTa.TheoremMetadata
import Mettapedia.Languages.MeTTa.PeTTa.SharedSourceExecution

/-!
# Actual theorem publication in the authored HOL checker

Publication retains the theorem payload, stores the command origin and records
the source rule's ordered premise occurrences. Both the receipt address and
the cache address must be fresh. These execution laws do not confer validity
on theorem-shaped input data; logical authorization is retained separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Publication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)

def value (hypotheses conclusion dependencies origin : Atom) : Atom :=
  .expression [.symbol "HOL:Thm", hypotheses, conclusion, dependencies, origin]

def publishedValue (key request hypotheses conclusion dependencies : Atom) : Atom :=
  value hypotheses conclusion dependencies (.expression [.symbol "HOL:Origin", key, request])

def afterState (operators constants axioms key request hypotheses conclusion dependencies : Atom)
    (parents : List Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Atom :=
  ProofLookup.sourceState operators constants axioms
    (ReceiptKeys.table (⟨key, request, parents⟩ :: receipts))
    ((key, publishedValue key request hypotheses conclusion dependencies) :: cache)

def result (operators constants axioms key request hypotheses conclusion dependencies : Atom)
    (parents : List Atom) (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Atom :=
  if ReceiptKeys.presentB key receipts then .symbol "None"
  else if cache.lookup key = none then
    .expression [.symbol "Some", afterState operators constants axioms key request hypotheses conclusion dependencies parents cache receipts]
  else .symbol "None"

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:publish"))[0]'(by decide)
private def publicationBody : Atom := .expression [.symbol "Some",
  .expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms",
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", .var "key",
      .expression [.symbol "HOL:Thm", .var "hyps", .var "conclusion", .var "dependencies",
        .expression [.symbol "HOL:Origin", .var "key", .var "request"]]], .var "cache"],
    .expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Receipt", .var "key", .var "request",
      .expression [.symbol "hol-light:premises", .var "request"]], .var "receipts"]]]
private def lookupCases : SpaceSemantics.Cases :=
  [(.symbol "None", publicationBody), (.var "duplicate", .symbol "None")]
private def lookupBody : Atom := .expression [.symbol "case",
  .expression [.symbol "hol-light:lookup", .var "key", .var "cache"],
  .expression (lookupCases.map fun row => .expression [row.1,row.2])]
private def theoremCases : SpaceSemantics.Cases :=
  [(.expression [.symbol "Some", .expression [.symbol "HOL:Thm", .var "hyps", .var "conclusion",
      .var "dependencies", .var "origin"]], lookupBody), (.var "refused", .symbol "None")]
private def theoremBody : Atom := .expression [.symbol "case", .var "result",
  .expression (theoremCases.map fun row => .expression [row.1,row.2])]
private def environment (operators constants axioms key request supplied : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Subst :=
  [("result", supplied), ("request", request), ("key", key), ("receipts", ReceiptKeys.table receipts),
    ("cache", Lookup.table cache), ("axioms", axioms), ("constants", constants), ("operators", operators)]
private def theoremEnvironment (operators constants axioms key request hypotheses conclusion dependencies origin : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) : Subst :=
  [("origin", origin), ("dependencies", dependencies), ("conclusion", conclusion), ("hyps", hypotheses)] ++
    environment operators constants axioms key request (.expression [.symbol "Some", value hypotheses conclusion dependencies origin]) cache receipts
private theorem shape : equation.body = .expression [.symbol "if",
    .expression [.symbol "hol-light:receipt-key-present", .var "key", .var "receipts"],
    .symbol "None", theoremBody] := by decide
private theorem clause (operators constants axioms key request supplied : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) :
    clauses program "hol-light:publish"
      [ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache, key, request, supplied] =
      [.evaluate (environment operators constants axioms key request supplied cache receipts) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:publish") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments = [.expression [.symbol "HOL:State", .var "operators", .var "constants", .var "axioms",
      .var "cache", .var "receipts"], .var "key", .var "request", .var "result"] := by decide
  simp [formals, ProofLookup.sourceState, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem insertion_returns (fragment : SharedSourceExecution.Fragment) (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (request : Atom) (parents : List Atom)
    (premisesComputed : ∀ (bindings : Subst) (state : State),
      applySubst bindings (.var "request") = request →
      SharedSourceExecution.PureReturns fragment program bindings state (.expression [.symbol "hol-light:premises", .var "request"]) state (Premises.keys parents))
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry) (state : State) :
    SharedSourceExecution.PureReturns fragment program
      (theoremEnvironment operators constants axioms key request
        hypotheses conclusion dependencies origin cache receipts) state publicationBody state
      (.expression [.symbol "Some", afterState operators constants axioms key request
        hypotheses conclusion dependencies parents cache receipts]) := by
  let bound := theoremEnvironment operators constants axioms key request hypotheses conclusion dependencies origin cache receipts
  unfold publicationBody
  apply SharedSourceExecution.unary_constructor_of_returns fragment program bound state state "Some" _ _ (by decide) (by decide)
  unfold afterState ProofLookup.sourceState
  apply SharedSourceExecution.constructor_return fragment program bound state "HOL:State" _ _ (by decide) (by decide)
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))
  · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "operators"
  · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "constants"
  · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "axioms"
  · change SharedSourceExecution.PureReturns fragment program bound state _ state
      (.expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Entry", key,
        publishedValue key request hypotheses conclusion dependencies], Lookup.table cache])
    apply SharedSourceExecution.constructor_return fragment program bound state "HOL:Cons" _ _ (by decide) (by decide)
    refine .cons ?_ (.cons ?_ .nil)
    · apply SharedSourceExecution.constructor_return fragment program bound state "HOL:Entry" _ _ (by decide) (by decide)
      refine .cons ?_ (.cons ?_ .nil)
      · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "key"
      · unfold publishedValue value
        apply SharedSourceExecution.constructor_return fragment program bound state "HOL:Thm" _ _ (by decide) (by decide)
        refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
        · simpa [bound, theoremEnvironment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "hyps"
        · simpa [bound, theoremEnvironment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "conclusion"
        · simpa [bound, theoremEnvironment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "dependencies"
        · apply SharedSourceExecution.constructor_return fragment program bound state "HOL:Origin" _ _ (by decide) (by decide)
          refine .cons ?_ (.cons ?_ .nil)
          · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "key"
          · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "request"
    · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "cache"
  · change SharedSourceExecution.PureReturns fragment program bound state _ state
      (.expression [.symbol "HOL:Cons", ReceiptKeys.entryAtom ⟨key, request, parents⟩,
        ReceiptKeys.table receipts])
    apply SharedSourceExecution.constructor_return fragment program bound state "HOL:Cons" _ _ (by decide) (by decide)
    refine .cons ?_ (.cons ?_ .nil)
    · unfold ReceiptKeys.entryAtom
      apply SharedSourceExecution.constructor_return fragment program bound state "HOL:Receipt" _ _ (by decide) (by decide)
      refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
      · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "key"
      · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "request"
      · exact premisesComputed bound state
          (by simp [bound, theoremEnvironment, environment, applySubst, Subst.lookup])
    · simpa [bound, theoremEnvironment, environment, applySubst, Subst.lookup] using SharedSourceExecution.variable_returns fragment program bound state "receipts"

private theorem body_returns (fragment : SharedSourceExecution.Fragment) (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (request : Atom) (parents : List Atom)
    (premisesComputed : ∀ (bindings : Subst) (state : State),
      applySubst bindings (.var "request") = request →
      SharedSourceExecution.PureReturns fragment program bindings state (.expression [.symbol "hol-light:premises", .var "request"]) state (Premises.keys parents)) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (state : State) :
    SharedSourceExecution.PureReturns fragment program (environment operators constants axioms key request
      (.expression [.symbol "Some", value hypotheses conclusion dependencies origin]) cache receipts) state equation.body state
      (result operators constants axioms key request
        hypotheses conclusion dependencies parents cache receipts) := by
  let before := environment operators constants axioms key request
    (.expression [.symbol "Some", value hypotheses conclusion dependencies origin]) cache receipts
  let bound := theoremEnvironment operators constants axioms key request hypotheses conclusion dependencies origin cache receipts
  rw [shape]
  apply SharedSourceExecution.if_returns fragment program before state state state _ (boolean (ReceiptKeys.presentB key receipts)) _ _ _
  · exact SharedSourceExecution.from_certificate fragment (ReceiptKeys.authored_receipt_key_present_certificate before state key receipts "key" "receipts"
      (by simp [before, environment, applySubst, Subst.lookup]) (by simp [before, environment, applySubst, Subst.lookup]))
  · cases present : ReceiptKeys.presentB key receipts
    · simp only [boolean, result, present]
      unfold theoremBody
      apply SharedSourceExecution.case_returns fragment program before bound state state state (.var "result")
        (.expression [.symbol "Some", value hypotheses conclusion dependencies origin]) lookupBody _ _ theoremCases
        (read_cases_encoded theoremCases)
      · exact SharedSourceExecution.variable_returns fragment program before state "result"
      · simp [theoremCases, value, bound, theoremEnvironment, before, environment, SpaceSemantics.selectCase,
          SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
      · unfold lookupBody
        cases cached : cache.lookup key with
        | none =>
            simp only [↓reduceIte]
            apply SharedSourceExecution.case_returns fragment program bound bound state state state
              (.expression [.symbol "hol-light:lookup", .var "key", .var "cache"]) (.symbol "None") publicationBody
              _ _ lookupCases (read_cases_encoded lookupCases)
            · simpa only [cached, Lookup.answer] using SharedSourceExecution.from_certificate fragment (Lookup.authored_lookup_certificate bound state key cache "key" "cache"
                (by simp [bound, theoremEnvironment, environment, applySubst, Subst.lookup])
                (by simp [bound, theoremEnvironment, environment, applySubst, Subst.lookup]))
            · simp [lookupCases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
            · exact insertion_returns fragment operators constants axioms key hypotheses conclusion dependencies origin request parents premisesComputed cache receipts state
        | some previous =>
            simp only [Option.some_ne_none, ↓reduceIte]
            let refused := ("duplicate", Atom.expression [.symbol "Some", previous]) :: bound
            apply SharedSourceExecution.case_returns fragment program bound refused state state state
              (.expression [.symbol "hol-light:lookup", .var "key", .var "cache"])
              (.expression [.symbol "Some", previous]) (.symbol "None") _ _ lookupCases (read_cases_encoded lookupCases)
            · simpa only [cached, Lookup.answer] using SharedSourceExecution.from_certificate fragment (Lookup.authored_lookup_certificate bound state key cache "key" "cache"
                (by simp [bound, theoremEnvironment, environment, applySubst, Subst.lookup])
                (by simp [bound, theoremEnvironment, environment, applySubst, Subst.lookup]))
            · simp [lookupCases, refused, bound, theoremEnvironment, environment, SpaceSemantics.selectCase,
                SpaceSemantics.matchValue, matchAtom, Subst.lookup]
            · exact SharedSourceExecution.symbol_returns fragment program refused state "None"
    · simpa only [result, present, ↓reduceIte, boolean, BEq.rfl] using SharedSourceExecution.symbol_returns fragment program before state "None"

/-- Actual publication either retains the complete payload and records the
command with its ordered premises, or refuses an occupied address. -/
theorem authored_publish_request_return (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (request : Atom) (parents : List Atom)
    (premisesComputed : ∀ (bindings : Subst) (state : State),
      applySubst bindings (.var "request") = request →
      PureReturns program bindings state (.expression [.symbol "hol-light:premises", .var "request"]) state (Premises.keys parents)) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (bindings : Subst) (state : State)
    (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (resultCaptured : applySubst bindings (.var resultName) = .expression [.symbol "Some", value hypotheses conclusion dependencies origin]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName]) state
      (result operators constants axioms key request
        hypotheses conclusion dependencies parents cache receipts) := by
  apply authored_variable_call_returns program bindings
    (environment operators constants axioms key request
      (.expression [.symbol "Some", value hypotheses conclusion dependencies origin]) cache receipts) state state
    "hol-light:publish" [stateKey,keyName,requestName,resultName] equation.body _
    (by decide) (by decide) (by decide) _
    (body_returns .original operators constants axioms key hypotheses conclusion dependencies origin request parents premisesComputed cache receipts state)
    (by decide)
  simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured, resultCaptured] using
    clause operators constants axioms key request
      (.expression [.symbol "Some", value hypotheses conclusion dependencies origin]) cache receipts

/-- The ten primitive inference requests instantiate general captured publication. -/
theorem authored_publish_theorem_return (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (bindings : Subst) (state : State)
    (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (resultCaptured : applySubst bindings (.var resultName) = .expression [.symbol "Some", value hypotheses conclusion dependencies origin]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName]) state
      (result operators constants axioms key (Premises.request kind payload first second)
        hypotheses conclusion dependencies (Premises.occurrences kind first second) cache receipts) := by
  exact authored_publish_request_return operators constants axioms key hypotheses conclusion dependencies origin
    (Premises.request kind payload first second) (Premises.occurrences kind first second)
    (fun bound phase captured => Premises.authored_premises_return bound phase kind payload first second "request" captured)
    cache receipts bindings state stateKey keyName requestName resultName stateCaptured keyCaptured requestCaptured resultCaptured

/-- Actual computation of a theorem payload precedes the publisher's
internal freshness checks, for any request with proved premise execution. -/
theorem authored_publish_computed_request_return (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (request : Atom) (parents : List Atom)
    (premisesComputed : ∀ (bindings : Subst) (state : State),
      applySubst bindings (.var "request") = request →
      PureReturns program bindings state (.expression [.symbol "hol-light:premises", .var "request"]) state (Premises.keys parents)) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (bindings : Subst) (state : State)
    (stateKey keyName requestName : String) (computedExpression : Atom)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (inferred : PureReturns program bindings state
      computedExpression state
      (.expression [.symbol "Some", value hypotheses conclusion dependencies origin])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName,
      computedExpression]) state
      (result operators constants axioms key request
        hypotheses conclusion dependencies parents cache receipts) := by
  let source := ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache
  let supplied := Atom.expression [.symbol "Some", value hypotheses conclusion dependencies origin]
  apply call_returns program bindings state state "hol-light:publish" _ _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    (.var stateKey) source _ _ [] 0 (by decide)
    (by simpa only [stateCaptured] using variable_returns program bindings state stateKey)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    (.var keyName) key _ _ [source] 1 (by decide)
    (by simpa only [keyCaptured] using variable_returns program bindings state keyName)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    (.var requestName) request _ _ [source,key] 2 (by decide)
    (by simpa only [requestCaptured] using variable_returns program bindings state requestName)
  apply evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    computedExpression supplied _ [] [source,key,request] 3
    (by decide) inferred
  exact authored_function_arguments_return program bindings
    (environment operators constants axioms key request supplied cache receipts) state state "hol-light:publish"
    [source,key,request,supplied] 4 equation.body _ (by decide) (by decide)
    (clause operators constants axioms key request supplied cache receipts)
    (body_returns .original operators constants axioms key hypotheses conclusion dependencies origin request parents premisesComputed cache receipts state)

/-- A certified publisher body composes with an actual computed payload in
the captured-call machine. The source premise computation is retained, and
occupied receipt or cache addresses still refuse insertion. -/
theorem authored_publish_computed_request_bound_return
    (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (request : Atom) (parents : List Atom)
    (premisesComputed : ∀ (bindings : Subst) (state : State),
      applySubst bindings (.var "request") = request →
      BoundCalls.CorePath.PureReturns program bindings state
        (.expression [.symbol "hol-light:premises", .var "request"]) state (Premises.keys parents))
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (computedExpression : Atom)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState
      operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (inferred : BoundCalls.PureReturns program bindings state computedExpression state
      (.expression [.symbol "Some", value hypotheses conclusion dependencies origin])) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, computedExpression]) state
      (result operators constants axioms key request hypotheses conclusion dependencies parents cache receipts) := by
  let supplied := Atom.expression [.symbol "Some", value hypotheses conclusion dependencies origin]
  apply BoundCalls.authored_prefix_call_returns program bindings
    (environment operators constants axioms key request supplied cache receipts)
    state state state "hol-light:publish" [stateKey,keyName,requestName] computedExpression supplied equation.body
    _ (by decide) (by decide) (by decide) (by rfl)
    (by change Eval.argumentIsRaw program "hol-light:publish" 3 = false; decide) inferred _
    (body_returns .conservative operators constants axioms key hypotheses conclusion dependencies origin
      request parents premisesComputed cache receipts state).extended
  simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured,
    List.cons_append, List.nil_append] using
    clause operators constants axioms key request supplied cache receipts

/-- All four actual arguments execute in order before the publisher enters
its own receipt and cache checks, including a computed command constructor. -/
theorem authored_publish_computed_arguments_bound_return
    (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (request : Atom) (parents : List Atom)
    (premisesComputed : ∀ (bindings : Subst) (state : State),
      applySubst bindings (.var "request") = request →
      BoundCalls.CorePath.PureReturns program bindings state
        (.expression [.symbol "hol-light:premises", .var "request"]) state (Premises.keys parents))
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateExpression keyExpression requestExpression resultExpression : Atom)
    (stateReturned : BoundCalls.PureReturns program bindings state stateExpression state
      (ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache))
    (keyReturned : BoundCalls.PureReturns program bindings state keyExpression state key)
    (requestReturned : BoundCalls.PureReturns program bindings state requestExpression state request)
    (resultReturned : BoundCalls.PureReturns program bindings state resultExpression state
      (.expression [.symbol "Some", value hypotheses conclusion dependencies origin])) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:publish", stateExpression, keyExpression, requestExpression, resultExpression]) state
      (result operators constants axioms key request hypotheses conclusion dependencies parents cache receipts) := by
  let world := ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache
  let supplied := Atom.expression [.symbol "Some", value hypotheses conclusion dependencies origin]
  apply BoundCalls.call_returns program bindings state state "hol-light:publish" _ _ (by decide) _ (by decide)
  apply BoundCalls.evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    stateExpression world _ [keyExpression, requestExpression, resultExpression] [] 0 (by decide) stateReturned
  apply BoundCalls.evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    keyExpression key _ [requestExpression, resultExpression] [world] 1 (by decide) keyReturned
  apply BoundCalls.evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    requestExpression request _ [resultExpression] [world, key] 2 (by decide) requestReturned
  apply BoundCalls.evaluated_argument_returns program bindings state state state (.function "hol-light:publish")
    resultExpression supplied _ [] [world, key, request] 3 (by decide) resultReturned
  exact BoundCalls.authored_function_arguments_return program bindings
    (environment operators constants axioms key request supplied cache receipts) state state
    "hol-light:publish" [world, key, request, supplied] 4 equation.body _ (by decide) (by decide)
    (clause operators constants axioms key request supplied cache receipts)
    (body_returns .conservative operators constants axioms key hypotheses conclusion dependencies origin
      request parents premisesComputed cache receipts state).extended

/-- The ten primitive inference requests instantiate general computed publication. -/
theorem authored_publish_inference_return (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (bindings : Subst) (state : State)
    (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (inferred : PureReturns program bindings state
      (.expression [.symbol "hol-light:infer", .var stateKey, .var requestName]) state
      (.expression [.symbol "Some", value hypotheses conclusion dependencies origin])) :
    PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName,
      .expression [.symbol "hol-light:infer", .var stateKey, .var requestName]]) state
      (result operators constants axioms key (Premises.request kind payload first second)
        hypotheses conclusion dependencies (Premises.occurrences kind first second) cache receipts) := by
  exact authored_publish_computed_request_return operators constants axioms key hypotheses conclusion dependencies origin
    (Premises.request kind payload first second) (Premises.occurrences kind first second)
    (fun bound phase captured => Premises.authored_premises_return bound phase kind payload first second "request" captured)
    cache receipts bindings state stateKey keyName requestName
    (.expression [.symbol "hol-light:infer", .var stateKey, .var requestName])
    stateCaptured keyCaptured requestCaptured inferred

/-- An occupied receipt address refuses publication regardless of the cache
or theorem payload. -/
theorem occupied_receipt_refused (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (occupied : ReceiptKeys.presentB key receipts = true)
    (bindings : Subst) (state : State) (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (resultCaptured : applySubst bindings (.var resultName) = .expression [.symbol "Some", value hypotheses conclusion dependencies origin]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName])
      state (.symbol "None") := by
  simpa only [result, occupied, ↓reduceIte] using authored_publish_theorem_return operators constants axioms key hypotheses
    conclusion dependencies origin kind payload first second cache receipts bindings state stateKey keyName requestName resultName
    stateCaptured keyCaptured requestCaptured resultCaptured

/-- Even with a fresh receipt address, any existing cache entry refuses
replacement. The cached value need not have theorem shape. -/
theorem occupied_cache_refused (operators constants axioms key hypotheses conclusion dependencies origin : Atom)
    (kind : InferenceKind) (payload first second : Atom) (cache : List (Atom × Atom))
    (receipts : List ReceiptKeys.Entry) (occupied : cache.lookup key ≠ none)
    (bindings : Subst) (state : State) (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = Premises.request kind payload first second)
    (resultCaptured : applySubst bindings (.var resultName) = .expression [.symbol "Some", value hypotheses conclusion dependencies origin]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName])
      state (.symbol "None") := by
  have returned := authored_publish_theorem_return operators constants axioms key hypotheses conclusion dependencies origin kind payload
    first second cache receipts bindings state stateKey keyName requestName resultName stateCaptured keyCaptured requestCaptured resultCaptured
  cases present : ReceiptKeys.presentB key receipts with
  | false => simpa only [result, present, Bool.false_eq_true, occupied, ↓reduceIte] using returned
  | true => simpa only [result, present, ↓reduceIte] using returned

private theorem refused_body_certificate (operators constants axioms key request : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (state : State) :
    BoundCalls.CorePath.PureReturns program
      (environment operators constants axioms key request (.symbol "None") cache receipts) state equation.body
      state (.symbol "None") := by
  let before := environment operators constants axioms key request (.symbol "None") cache receipts
  rw [shape]
  apply BoundCalls.CorePath.if_returns program before state state state _ (boolean (ReceiptKeys.presentB key receipts)) _ _ _
  · exact ReceiptKeys.authored_receipt_key_present_certificate before state key receipts "key" "receipts"
      (by simp [before, environment, applySubst, Subst.lookup]) (by simp [before, environment, applySubst, Subst.lookup])
  · cases present : ReceiptKeys.presentB key receipts with
    | false =>
        simp only [boolean]
        let refused := ("refused", Atom.symbol "None") :: before
        unfold theoremBody
        apply BoundCalls.CorePath.case_returns program before refused state state state (.var "result") (.symbol "None") (.symbol "None")
          _ _ theoremCases (read_cases_encoded theoremCases)
        · exact BoundCalls.CorePath.variable_returns program before state "result"
        · simp [theoremCases, refused, before, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
        · exact BoundCalls.CorePath.symbol_returns program refused state "None"
    | true => simpa only [boolean, BEq.rfl, ↓reduceIte] using BoundCalls.CorePath.symbol_returns program before state "None"

/-- The refusal path has a conservative certificate independently of both
address tables. It checks the actual result case before cache lookup. -/
theorem authored_publish_refused_certificate (operators constants axioms key request : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (resultCaptured : applySubst bindings (.var resultName) = .symbol "None") :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName])
      state (.symbol "None") := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings
    (environment operators constants axioms key request (.symbol "None") cache receipts) state state "hol-light:publish"
    [stateKey,keyName,requestName,resultName] equation.body _ (by decide) (by decide) (by decide) _
    (refused_body_certificate operators constants axioms key request cache receipts state) (by decide)
  simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured, resultCaptured] using
    clause operators constants axioms key request (.symbol "None") cache receipts

/-- A computed refusal is supplied as the publisher's actual final argument.
The nested computation's path is retained; no textual replacement is assumed. -/
theorem authored_publish_computed_refused_bound_return (operators constants axioms key request argument : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (computed : BoundCalls.PureReturns program bindings state argument state (.symbol "None")) :
    BoundCalls.PureReturns program bindings state
      (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, argument])
      state (.symbol "None") := by
  apply BoundCalls.authored_prefix_call_returns program bindings
    (environment operators constants axioms key request (.symbol "None") cache receipts)
    state state state "hol-light:publish" [stateKey,keyName,requestName] argument (.symbol "None") equation.body
    (.symbol "None") (by decide) (by decide) (by decide) (by rfl)
    (by change Eval.argumentIsRaw program "hol-light:publish" 3 = false; decide) computed _
    (refused_body_certificate operators constants axioms key request cache receipts state).extended
  simpa only [List.map_cons, List.map_nil, stateCaptured, keyCaptured, requestCaptured, List.cons_append, List.nil_append] using
    clause operators constants axioms key request (.symbol "None") cache receipts

/-- A refused result cannot be inserted by the original source machine. -/
theorem authored_publish_refused_return (operators constants axioms key request : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (resultCaptured : applySubst bindings (.var resultName) = .symbol "None") :
    PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName])
      state (.symbol "None") :=
  (authored_publish_refused_certificate operators constants axioms key request cache receipts bindings state
    stateKey keyName requestName resultName stateCaptured keyCaptured requestCaptured resultCaptured).original

/-- The constructed refusal also executes in the captured-call machine. -/
theorem authored_publish_refused_bound_return (operators constants axioms key request : Atom)
    (cache : List (Atom × Atom)) (receipts : List ReceiptKeys.Entry)
    (bindings : Subst) (state : State) (stateKey keyName requestName resultName : String)
    (stateCaptured : applySubst bindings (.var stateKey) = ProofLookup.sourceState operators constants axioms (ReceiptKeys.table receipts) cache)
    (keyCaptured : applySubst bindings (.var keyName) = key)
    (requestCaptured : applySubst bindings (.var requestName) = request)
    (resultCaptured : applySubst bindings (.var resultName) = .symbol "None") :
    BoundCalls.PureReturns program bindings state (.expression [.symbol "hol-light:publish", .var stateKey, .var keyName, .var requestName, .var resultName])
      state (.symbol "None") :=
  (authored_publish_refused_certificate operators constants axioms key request cache receipts bindings state
    stateKey keyName requestName resultName stateCaptured keyCaptured requestCaptured resultCaptured).extended

end Mettapedia.Languages.HOLLight.MeTTa.Publication
