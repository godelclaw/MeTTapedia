import Mettapedia.Languages.HOLLight.MeTTa.Program
import Mettapedia.Languages.HOLLight.Rules
import Mettapedia.Languages.MeTTa.PeTTa.CoreExecution

/-!
# Ordered premise occurrences computed by the authored MeTTa program

This proof executes the retained `hol-light:premises` body through PeTTa's
existing evaluation relation. It covers every primitive inference kind and
arbitrary captured proof keys. It proves the receipt component, not the
logical correctness of the whole MeTTa checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.Premises

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)

def keys : List Atom → Atom
  | [] => .symbol "HOL:Nil"
  | first :: rest => .expression [.symbol "HOL:Cons", first, keys rest]

/-- Payload is the source term, abstraction variable or substitution data;
first and second are cache references, not caller-supplied theorem records. -/
def request (kind : InferenceKind) (payload first second : Atom) : Atom :=
  match kind with
  | .refl => .expression [.symbol "REFL", payload]
  | .trans => .expression [.symbol "TRANS", first, second]
  | .mkComb => .expression [.symbol "MK_COMB", first, second]
  | .abs => .expression [.symbol "ABS", payload, first]
  | .beta => .expression [.symbol "BETA", payload]
  | .assume => .expression [.symbol "ASSUME", payload]
  | .eqMp => .expression [.symbol "EQ_MP", first, second]
  | .deductAntisym => .expression [.symbol "DEDUCT_ANTISYM_RULE", first, second]
  | .instType => .expression [.symbol "INST_TYPE", payload, first]
  | .inst => .expression [.symbol "INST", payload, first]

def occurrences (kind : InferenceKind) (first second : Atom) : List Atom :=
  match kind with
  | .refl | .beta | .assume => []
  | .trans | .mkComb | .eqMp | .deductAntisym => [first, second]
  | .abs | .instType | .inst => [first]

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter
    (fun row => row.head == "hol-light:premises"))[0]'(by decide)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def pairBody : Atom :=
  .expression [.symbol "HOL:Cons", .var "first",
    .expression [.symbol "HOL:Cons", .var "second", .symbol "HOL:Nil"]]

private def singleBody : Atom :=
  .expression [.symbol "HOL:Cons", .var "premise", .symbol "HOL:Nil"]

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "hol-light:premises") = [equation] := by
  rfl

private theorem formals : equation.arguments = [.var "request"] := by decide

private theorem body_shape : equation.body =
    .expression [.symbol "case", .var "request",
      .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem cases_shape : cases =
    [(.expression [.symbol "TRANS", .var "first", .var "second"], pairBody),
     (.expression [.symbol "MK_COMB", .var "first", .var "second"], pairBody),
     (.expression [.symbol "EQ_MP", .var "first", .var "second"], pairBody),
     (.expression [.symbol "DEDUCT_ANTISYM_RULE", .var "first", .var "second"], pairBody),
     (.expression [.symbol "ABS", .var "variable", .var "premise"], singleBody),
     (.expression [.symbol "INST", .var "entries", .var "premise"], singleBody),
     (.expression [.symbol "INST_TYPE", .var "entries", .var "premise"], singleBody),
     (.expression [.symbol "TYPE_DEFINITION", .var "name", .var "abs", .var "rep", .var "premise"], singleBody),
     (.var "noPremises", .symbol "HOL:Nil")] := by decide

private def environment (kind : InferenceKind) (payload first second : Atom) : Subst :=
  [("request", request kind payload first second)]

private def branchEnvironment (kind : InferenceKind) (payload first second : Atom) : Subst :=
  (match kind with
   | .trans | .mkComb | .eqMp | .deductAntisym =>
       [("second", second), ("first", first)]
   | .abs => [("premise", first), ("variable", payload)]
   | .inst | .instType => [("premise", first), ("entries", payload)]
   | .refl | .beta | .assume => [("noPremises", request kind payload first second)]) ++
    environment kind payload first second

private def branchBody : InferenceKind → Atom
  | .refl | .beta | .assume => .symbol "HOL:Nil"
  | .trans | .mkComb | .eqMp | .deductAntisym => pairBody
  | .abs | .inst | .instType => singleBody

private theorem selected (kind : InferenceKind) (payload first second : Atom) :
    SpaceSemantics.selectCase (environment kind payload first second)
      (request kind payload first second) cases =
        some (branchEnvironment kind payload first second, branchBody kind) := by
  cases kind <;>
    simp [cases_shape, environment, branchEnvironment, branchBody, request,
      SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem single_returns (bindings : Subst) (state : State) (value : Atom)
    (captured : applySubst bindings (.var "premise") = value) :
    BoundCalls.CorePath.PureReturns program bindings state singleBody state (keys [value]) := by
  unfold singleBody
  apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state "HOL:Cons"
    (.var "premise") (.symbol "HOL:Nil") value (.symbol "HOL:Nil")
    (by decide) (by decide)
  · simpa only [captured] using BoundCalls.CorePath.variable_returns program bindings state "premise"
  · exact BoundCalls.CorePath.symbol_returns program bindings state "HOL:Nil"

private theorem pair_returns (bindings : Subst) (state : State) (first second : Atom)
    (capturedFirst : applySubst bindings (.var "first") = first)
    (capturedSecond : applySubst bindings (.var "second") = second) :
    BoundCalls.CorePath.PureReturns program bindings state pairBody state (keys [first, second]) := by
  unfold pairBody
  apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state "HOL:Cons"
    (.var "first") (.expression [.symbol "HOL:Cons", .var "second", .symbol "HOL:Nil"])
    first (keys [second]) (by decide) (by decide)
  · simpa only [capturedFirst] using BoundCalls.CorePath.variable_returns program bindings state "first"
  · apply BoundCalls.CorePath.binary_constructor_returns program bindings state state state "HOL:Cons"
      (.var "second") (.symbol "HOL:Nil") second (.symbol "HOL:Nil")
      (by decide) (by decide)
    · simpa only [capturedSecond] using BoundCalls.CorePath.variable_returns program bindings state "second"
    · exact BoundCalls.CorePath.symbol_returns program bindings state "HOL:Nil"

private theorem branch_returns (kind : InferenceKind) (payload first second : Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (branchEnvironment kind payload first second) state
      (branchBody kind) state (keys (occurrences kind first second)) := by
  cases kind <;> simp only [branchBody, occurrences]
  · exact BoundCalls.CorePath.symbol_returns program _ state "HOL:Nil"
  · exact pair_returns _ state first second rfl rfl
  · exact pair_returns _ state first second rfl rfl
  · exact single_returns _ state first rfl
  · exact BoundCalls.CorePath.symbol_returns program _ state "HOL:Nil"
  · exact BoundCalls.CorePath.symbol_returns program _ state "HOL:Nil"
  · exact pair_returns _ state first second rfl rfl
  · exact pair_returns _ state first second rfl rfl
  · exact single_returns _ state first rfl
  · exact single_returns _ state first rfl

private theorem body_returns (kind : InferenceKind) (payload first second : Atom) (state : State) :
    BoundCalls.CorePath.PureReturns program (environment kind payload first second) state equation.body state
      (keys (occurrences kind first second)) := by
  rw [body_shape]
  apply BoundCalls.CorePath.case_returns program (environment kind payload first second)
    (branchEnvironment kind payload first second) state state state
    (.var "request") (request kind payload first second) (branchBody kind) _ _ cases
    (read_cases_encoded cases)
  · exact BoundCalls.CorePath.variable_returns program _ state "request"
  · exact selected kind payload first second
  · exact branch_returns kind payload first second state

private theorem clause (kind : InferenceKind) (payload first second : Atom) :
    clauses program "hol-light:premises" [request kind payload first second] =
      [.evaluate (environment kind payload first second) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Actual authored evaluation computes the source rule's ordered proof keys,
for all ten inference kinds, with the store unchanged. -/
theorem authored_premises_certificate (bindings : Subst) (state : State)
    (kind : InferenceKind) (payload first second : Atom) (name : String)
    (captured : applySubst bindings (.var name) = request kind payload first second) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:premises", .var name]) state
      (keys (occurrences kind first second)) := by
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings (environment kind payload first second)
    state state "hol-light:premises" [name] equation.body _
    (by decide) (by decide) (by decide) _ (body_returns kind payload first second state) (by decide)
  simpa only [List.map_cons, List.map_nil, captured] using clause kind payload first second

/-- An axiom event retains its commitment dependency separately from proof
premise addresses. The actual source helper returns no proof addresses. -/
theorem authored_axiom_premises_certificate (bindings : Subst) (state : State)
    (label source : Atom) (name : String)
    (captured : applySubst bindings (.var name) = .expression [.symbol "AXIOM", label, source]) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:premises", .var name]) state (keys []) := by
  let request := Atom.expression [.symbol "AXIOM", label, source]
  let before : Subst := [("request", request)]
  let bound : Subst := ("noPremises", request) :: before
  have actualClause : clauses program "hol-light:premises" [request] = [.evaluate before equation.body] := by
    rw [clauses_use_only_the_named_equations, equation_unique]
    simp [formals, before, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings before state state "hol-light:premises" [name]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, captured] using actualClause
  · rw [body_shape]
    apply BoundCalls.CorePath.case_returns program before bound state state state (.var "request") request (.symbol "HOL:Nil")
      _ _ cases (read_cases_encoded cases) (BoundCalls.CorePath.variable_returns program before state "request") _
      (BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil")
    simp [cases_shape, before, bound, request, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- A constant-definition command constructs its own equation and names no
cached proof premise. The actual source helper executes that distinction. -/
theorem authored_definition_premises_certificate (bindings : Subst) (state : State)
    (constant schema source : Atom) (name : String)
    (captured : applySubst bindings (.var name) = .expression [.symbol "DEFINITION", constant, schema, source]) :
    BoundCalls.CorePath.PureReturns program bindings state (.expression [.symbol "hol-light:premises", .var name]) state (keys []) := by
  let request := Atom.expression [.symbol "DEFINITION", constant, schema, source]
  let before : Subst := [("request", request)]
  let bound : Subst := ("noPremises", request) :: before
  have actualClause : clauses program "hol-light:premises" [request] = [.evaluate before equation.body] := by
    rw [clauses_use_only_the_named_equations, equation_unique]
    simp [formals, before, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings before state state "hol-light:premises" [name]
    equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, captured] using actualClause
  · rw [body_shape]
    apply BoundCalls.CorePath.case_returns program before bound state state state (.var "request") request (.symbol "HOL:Nil")
      _ _ cases (read_cases_encoded cases) (BoundCalls.CorePath.variable_returns program before state "request") _
      (BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil")
    simp [cases_shape, before, bound, request, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- Each type-definition law records the actual existence-proof address.
The declaration names are payload, not extra proof premises. -/
theorem authored_type_definition_premises_certificate (bindings : Subst) (state : State)
    (typeName abstractionName representationName premise : Atom) (name : String)
    (captured : applySubst bindings (.var name) =
      .expression [.symbol "TYPE_DEFINITION", typeName, abstractionName, representationName, premise]) :
    BoundCalls.CorePath.PureReturns program bindings state
      (.expression [.symbol "hol-light:premises", .var name]) state (keys [premise]) := by
  let command := Atom.expression [.symbol "TYPE_DEFINITION", typeName, abstractionName, representationName, premise]
  let before : Subst := [("request", command)]
  let bound : Subst := [("premise", premise), ("rep", representationName),
    ("abs", abstractionName), ("name", typeName)] ++ before
  have actualClause : clauses program "hol-light:premises" [command] = [.evaluate before equation.body] := by
    rw [clauses_use_only_the_named_equations, equation_unique]
    simp [formals, before, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
  apply BoundCalls.CorePath.authored_variable_call_returns program bindings before state state
    "hol-light:premises" [name] equation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa only [List.map_cons, List.map_nil, captured] using actualClause
  · rw [body_shape]
    apply BoundCalls.CorePath.case_returns program before bound state state state (.var "request") command
      singleBody _ _ cases (read_cases_encoded cases)
    · exact BoundCalls.CorePath.variable_returns program before state "request"
    · simp [cases_shape, before, bound, command, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
    · unfold singleBody keys
      apply BoundCalls.CorePath.binary_constructor_returns program bound state state state "HOL:Cons"
        (.var "premise") (.symbol "HOL:Nil") premise (.symbol "HOL:Nil") (by decide) (by decide)
      · simpa [bound, applySubst, Subst.lookup] using BoundCalls.CorePath.variable_returns program bound state "premise"
      · exact BoundCalls.CorePath.symbol_returns program bound state "HOL:Nil"

/-- The independently specified HOL rule has the same premise arity. -/
theorem occurrence_count_agrees (input : InferenceRequest) (first second : Atom) :
    (occurrences input.kind first second).length = input.premises.length := by
  cases input <;> rfl

/-- Reusing one key in two positions retains two occurrences. -/
theorem repeated_key_retained (key : Atom) :
    occurrences .trans key key = [key, key] ∧
      (occurrences .trans key key).length = 2 := by
  exact ⟨rfl, rfl⟩

theorem authored_premises_return (bindings : Subst) (state : State)
    (kind : InferenceKind) (payload first second : Atom) (name : String)
    (captured : applySubst bindings (.var name) = request kind payload first second) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:premises", .var name]) state
      (keys (occurrences kind first second)) :=
  (authored_premises_certificate bindings state kind payload first second name captured).original

/-- The original source interface projects the same constructed certificate. -/
theorem authored_axiom_premises_return (bindings : Subst) (state : State)
    (label source : Atom) (name : String)
    (captured : applySubst bindings (.var name) = .expression [.symbol "AXIOM", label, source]) :
    PureReturns program bindings state (.expression [.symbol "hol-light:premises", .var name]) state (keys []) :=
  (authored_axiom_premises_certificate bindings state label source name captured).original

end Mettapedia.Languages.HOLLight.MeTTa.Premises
