import Mettapedia.Languages.C11.FixedCoreServices
import Mettapedia.Languages.C11.CestaFixedCoreControls
import Mettapedia.Languages.MeTTa.HE.RecursiveService

/-!
# C programs served by the HE evaluator

C sources parsed by Cesta call functions they do not define. The calls are
served by the retained HE evaluator over a space of MeTTa equations: each
request becomes a MeTTa call on Peano numerals, the evaluator's result
occurrences are published inside the C program's trace, and a single readable
result is the C function's return value. A C loop calling a MeTTa function
three times returns what GCC computes for the same loop over a C definition of
that function, also when the MeTTa function is recursive and calls an equation
inside its own argument. Two results, or a result that is not a numeral, stop the C
program with the service's fault after both machines' events.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.FixedCoreServiceControls

open FixedCore FixedCoreControls CestaFixedCoreControls IntegerMemoryModel
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings GroundedDispatch ResultPair)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Parsing.CanonicalGrammar (CanonicalTerm)
open CestaFixedCore (readUnit Signature)

abbrev Failure := Mettapedia.Languages.MeTTa.HE.RecursiveService.Failure
abbrev ResourceRequest := Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Checked.ResourceRequest
abbrev Service := Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Configuration
abbrev Composed := HandledState (Executable model) Service (Request model)
abbrev Trace := Hosted model ResultPair Failure

/-! ## The MeTTa side -/

def zeroAtom : Atom := .symbol "Z"
def succAtom (atom : Atom) : Atom := .expression [.symbol "S", atom]
def callAtom (name : String) (arguments : List Atom) : Atom := .expression (.symbol name :: arguments)
def equation (left right : Atom) : Atom := .expression [.symbol "=", left, right]

def numeral : Nat → Atom
  | 0 => zeroAtom
  | count + 1 => succAtom (numeral count)

def numeral? : Atom → Option Nat
  | .symbol "Z" => some 0
  | .expression [.symbol "S", atom] => (numeral? atom).map (· + 1)
  | _ => none

/-- `(= (pred (S $n)) $n)`, `(= (plus3 $m) (S (S (S $m))))`,
`(= (step $x) (plus3 (pred (S $x))))`, `(= (coin) Z)`, `(= (coin) (S Z))`,
`(= (inc $x) (S $x))`, `(= (inc3 $x) (inc (inc (inc $x))))`, `(= (add Z $y) $y)`,
`(= (add (S $x) $y) (S (add $x $y)))`, `(= (grow $i $x) (add (inc3 $i) $x))`. -/
def space : Space := Space.ofList
  [equation (callAtom "pred" [succAtom (.var "n")]) (.var "n"),
    equation (callAtom "plus3" [.var "m"]) (succAtom (succAtom (succAtom (.var "m")))),
    equation (callAtom "step" [.var "x"]) (callAtom "plus3" [callAtom "pred" [succAtom (.var "x")]]),
    equation (callAtom "coin" []) zeroAtom,
    equation (callAtom "coin" []) (succAtom zeroAtom),
    equation (callAtom "inc" [.var "x"]) (succAtom (.var "x")),
    equation (callAtom "inc3" [.var "x"])
      (callAtom "inc" [callAtom "inc" [callAtom "inc" [.var "x"]]]),
    equation (callAtom "add" [zeroAtom, .var "y"]) (.var "y"),
    equation (callAtom "add" [succAtom (.var "x"), .var "y"])
      (succAtom (callAtom "add" [.var "x", .var "y"])),
    equation (callAtom "grow" [.var "i", .var "x"])
      (callAtom "add" [callAtom "inc3" [.var "i"], .var "x"])]

/-- A C integer argument is passed as a numeral when it is not negative. -/
def encode : Value model → Option Atom
  | .integer scalar => if 0 ≤ scalar.integer.value then some (numeral scalar.integer.value.toNat) else none
  | _ => none

/-- A numeral result is returned as a C `int` when it fits. -/
def decode (atom : Atom) : Option (Value model) := do
  let count ← numeral? atom
  let integer ← IntegerStep.decodeValue (IntegerType.int.format model.parameters) (Int.ofNat count)
  some (.integer ⟨.int, integer⟩)

/-- The evaluation depth budget of one request. -/
def depth : Nat := 128

/-- Each request is evaluated as the MeTTa call of its service on its arguments.
A request whose arguments have no MeTTa form has no result. -/
def load (request : Request model) : Service :=
  match request.arguments.mapM encode with
  | some arguments =>
      Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Configuration.initial space
        (.atom (callAtom request.service arguments) Atom.undefinedType Bindings.empty depth)
  | none => ⟨space, .returning [], [], []⟩

def mettaService : Machine Service Trace (Reply (Value model) Failure) ResourceRequest :=
  Mettapedia.Languages.MeTTa.HE.RecursiveService.service decode GroundedDispatch.none .foreign

/-! ## The composed program -/

def services : List (String × Signature) :=
  [("step", ⟨[.integer .int], some (.integer .int)⟩), ("coin", ⟨[], some (.integer .int)⟩),
    ("stuck", ⟨[], some (.integer .int)⟩),
    ("grow", ⟨[.integer .int, .integer .int], some (.integer .int)⟩)]

def composed (program : Program model)
    (serviceMachine : Machine Service Trace (Reply (Value model) Failure) ResourceRequest := mettaService) :
    Machine Composed Trace (Option (Value model)) ResourceRequest :=
  served model policy abi program serviceMachine load

/-- **A C call served by MeTTa publishes the evaluator's meaning.** When a C
request has a MeTTa form and its evaluation completes, the composed program
publishes the request, exactly the independent evaluator's result occurrences
and the reply computed from them, and resumes the C program with that reply. -/
theorem metta_call_publishes_evaluator_meaning (program : Program model)
    (configuration saved : Executable model) (request : Request model)
    (called : (machine model policy abi program).step configuration = some (.call request saved))
    (arguments : List Atom) (encoded : request.arguments.mapM encode = some arguments)
    (fuel : Nat) (events : List Trace) (reply : Reply (Value model) Failure)
    (answered : mettaService.run fuel (load request) = (events, .finished reply)) :
    let task := Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Task.atom
      (callAtom request.service arguments) Atom.undefinedType Bindings.empty depth
    let meaning := task.denote space GroundedDispatch.none
    ∃ used ≤ fuel + 1, (composed program).run used (.running configuration) =
      (.called request :: meaning.map .foreign ++
          [.replied (Mettapedia.Languages.MeTTa.HE.RecursiveService.answer decode meaning)],
        .exhausted (.running (resume model policy saved
          (Mettapedia.Languages.MeTTa.HE.RecursiveService.answer decode meaning)))) := by
  intro task meaning
  have loaded : load request = Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Configuration.initial space task := by
    simp only [load, encoded]
    rfl
  rw [loaded] at answered
  obtain ⟨rfl, rfl⟩ := Mettapedia.Languages.MeTTa.HE.RecursiveService.service_finished decode
    GroundedDispatch.none _ space task fuel events reply answered
  rw [← loaded] at answered
  exact served_call model policy abi program mettaService load configuration saved request called fuel _ _ answered

/-- The same C request loader served by the configuration-scoped HE worker. -/
def scopedMettaService : Machine Service Trace (Reply (Value model) Failure) ResourceRequest :=
  Mettapedia.Languages.MeTTa.HE.RecursiveService.checkedService decode
    Mettapedia.Languages.MeTTa.HE.FirstSuccessRecursiveExecution.scopedTypes
    GroundedDispatch.none .foreign

section ScopedSource

open Mettapedia.Languages.MeTTa.HE

private theorem space_closed_annotations : FirstSuccessScopedAdequacy.ClosedTypeAnnotations space :=
  (FirstSuccessScopedAdequacy.closedColonAnnotations_of_bool (by decide +kernel)).closedTypeAnnotations

/-- A covered independent HE source derivation constructs the complete C
service-call block. The reply and every published occurrence follow from
that derivation, without an assumed completed evaluator run. -/
theorem scoped_metta_call_source (program : Program model)
    (configuration saved : Executable model) (request : Request model)
    (called : (machine model policy abi program).step configuration = some (.call request saved))
    (arguments : List Atom) (encoded : request.arguments.mapM encode = some arguments)
    {comparison : SourceBindingComparison} {results : ResultSet}
    (source : FirstSuccessSourceExecution.AtomDerivation
      (comparison := comparison) space [] (callAtom request.service arguments)
      Atom.undefinedType Bindings.empty depth results)
    (covered : source.Covered) :
    ∃ used,
      (served model policy abi program scopedMettaService load).run used (.running configuration) =
        (.called request :: results.map .foreign ++ [.replied (RecursiveService.answer decode results)],
          .exhausted (.running (resume model policy saved (RecursiveService.answer decode results)))) := by
  have loaded : load request = RecursiveTasks.Configuration.initial space
      (.atom (callAtom request.service arguments) Atom.undefinedType Bindings.empty depth []) := by
    simp only [load,encoded]
  obtain ⟨budget,completed⟩ := RecursiveService.checked_service_source_completed decode
    (Event := Trace) .foreign source covered space_closed_annotations
  have answered : scopedMettaService.run budget (load request) =
      (results.map .foreign,.finished (RecursiveService.answer decode results)) := by
    rw [loaded]
    simpa only [scopedMettaService,Nat.add_zero] using completed 0
  obtain ⟨used,_,executed⟩ := served_call model policy abi program scopedMettaService load
    configuration saved request called budget _ _ answered
  exact ⟨used,executed⟩

/-- A real waiting C caller stays attached to the complete paused HE
configuration. Resumption emits only the remaining source occurrences and
one reply; it does not reload the request or replay its published prefix. -/
theorem scoped_metta_resume_source (program : Program model)
    (configuration saved : Executable model) (request : Request model)
    (called : (machine model policy abi program).step configuration = some (.call request saved))
    (arguments : List Atom) (encoded : request.arguments.mapM encode = some arguments)
    {comparison : SourceBindingComparison} {results : ResultSet}
    (source : FirstSuccessSourceExecution.AtomDerivation
      (comparison := comparison) space [] (callAtom request.service arguments)
      Atom.undefinedType Bindings.empty depth results)
    (covered : source.Covered) (first : Nat) (before : List Trace) (residual : Service)
    (paused : scopedMettaService.run first (load request) = (before,.exhausted residual)) :
    saved.status = .waiting request.service request.arguments ∧
      ∃ used after,
        (served model policy abi program scopedMettaService load).run used
          (.handling request saved residual) =
            (after ++ [.replied (RecursiveService.answer decode results)],
              .exhausted (.running (resume model policy saved (RecursiveService.answer decode results)))) ∧
        before ++ after = results.map .foreign := by
  have caller := call_saves_waiting model policy abi program configuration saved request called
  refine ⟨by rw [caller.1]; exact caller.2,?_⟩
  have loaded : load request = RecursiveTasks.Configuration.initial space
      (.atom (callAtom request.service arguments) Atom.undefinedType Bindings.empty depth []) := by
    simp only [load,encoded]
  have pausedWorker := paused
  rw [scopedMettaService,loaded] at pausedWorker
  obtain ⟨budget,after,completed,partition⟩ := RecursiveService.checked_service_source_resume decode
    (Event := Trace) .foreign source covered space_closed_annotations first before residual pausedWorker
  have completedService : scopedMettaService.run budget residual =
      (after,.finished (RecursiveService.answer decode results)) := completed
  obtain ⟨used,_,executed⟩ := (hosted model policy abi program).handle_run_of_reply
    (callback model policy) scopedMettaService load budget request saved residual after
      (RecursiveService.answer decode results) completedService
  exact ⟨used,after,executed,partition⟩

end ScopedSource

def runComposed (unit : CanonicalTerm) (fuel : Nat)
    (serviceMachine : Machine Service Trace (Reply (Value model) Failure) ResourceRequest := mettaService) :
    Option (List Trace × Outcome Composed (Option (Value model)) ResourceRequest) := do
  let program ← readUnit model services unit
  let initial ← start model program "main" ⟨[], []⟩ []
  some ((composed program serviceMachine).run fuel (.running initial))

def returnedValue : List Trace × Outcome Composed (Option (Value model)) ResourceRequest → Option Int
  | (_, .finished (some (.integer value))) => some value.integer.value
  | _ => none

def calls (events : List Trace) : Nat := (events.filter fun | .called _ => true | _ => false).length

def mettaResults (events : List Trace) : List Atom :=
  events.filterMap fun | .foreign result => some result.1 | _ => none

/-- The failures among the replies, and the number of replies. -/
def failedReplies (events : List Trace) : List Failure × Nat :=
  (events.filterMap fun | .replied (.faulted failure) => some failure | _ => none,
    (events.filter fun | .replied _ => true | _ => false).length)

def stoppedWith : List Trace × Outcome Composed (Option (Value model)) ResourceRequest → Option (Fault model)
  | (events, .faulted) =>
      match events.getLast? with
      | some (.core (.fault reason)) => some reason
      | _ => none
  | _ => none

/-- `int main(void) { int x = 0, i = 0; while (i < 3) { x = update; i = i + 1; } return x; }` -/
def loopUnit (update : CanonicalTerm) : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [
                      .node "InitDeclaratorValue" [
                        .node "Declarator" [.node "NameDeclarator" [.text "x"]],
                        .node "InitializerExpression" [.node "IntConst" [.text "0"]]],
                      .node "InitDeclaratorValue" [
                        .node "Declarator" [.node "NameDeclarator" [.text "i"]],
                        .node "InitializerExpression" [.node "IntConst" [.text "0"]]]]]]],
              .node "BlockStatement" [
                .node "IterationStatement" [
                  .node "While" [
                    .node "Less" [.node "Var" [.text "i"], .node "IntConst" [.text "3"]],
                    .node "CompoundStatement" [
                      .node "Block" [
                        .seq [
                          .node "BlockStatement" [
                            .node "ExpressionStatement" [
                              .node "SomeFullExpression" [
                                .node "Assign" [
                                  .node "Var" [.text "x"],
                                  update]]]],
                          .node "BlockStatement" [
                            .node "ExpressionStatement" [
                              .node "SomeFullExpression" [
                                .node "Assign" [
                                  .node "Var" [.text "i"],
                                  .node "Add" [.node "Var" [.text "i"], .node "IntConst" [.text "1"]]]]]]]]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "x"]]]]]]]]]]]

def callTerm (name : String) (arguments : List CanonicalTerm) : CanonicalTerm :=
  .node "Call" [.node "Var" [.text name], .node "Arguments" [.seq arguments]]

def variableTerm (name : String) : CanonicalTerm := .node "Var" [.text name]

/-- `x = step(x)` in the loop. -/
def servicesUnit : CanonicalTerm := loopUnit (callTerm "step" [variableTerm "x"])

/-- With `int step(int x) { return x + 3; }` GCC returns 9; three requests are
served by MeTTa and each publishes one numeral result. -/
theorem metta_served_loop_returns_nine :
    (runComposed servicesUnit 3000).map (fun run =>
      (returnedValue run, calls run.1, mettaResults run.1)) =
      some (some 9, 3, [numeral 3, numeral 6, numeral 9]) := by
  decide +kernel

/-- `x = grow(i, x)` in the loop, where `grow` is the MeTTa function
`(= (grow $i $x) (add (inc3 $i) $x))`: `inc3` calls `inc` inside its own
argument twice over, and `add` calls itself inside its result. With
`int grow(int i, int x) { return i + 3 + x; }` GCC returns 12; three requests
are served by MeTTa and each publishes exactly one numeral result. -/
def recursiveServicesUnit : CanonicalTerm :=
  loopUnit (callTerm "grow" [variableTerm "i", variableTerm "x"])

theorem recursive_metta_service_returns_twelve :
    (runComposed recursiveServicesUnit 12000).map (fun run =>
      (returnedValue run, calls run.1, mettaResults run.1)) =
      some (some 12, 3, [numeral 3, numeral 7, numeral 12]) := by
  decide +kernel

/-- The legacy finite approximation loses the last result at depth 64. This
empty approximation is not a completed failure of the checked service. -/
theorem shallow_budget_loses_last_request :
    (Mettapedia.Languages.MeTTa.HE.evalAtom space GroundedDispatch.none
        (callAtom "grow" [numeral 2, numeral 7]) Atom.undefinedType Bindings.empty 64,
      (Mettapedia.Languages.MeTTa.HE.evalAtom space GroundedDispatch.none
        (callAtom "grow" [numeral 2, numeral 7]) Atom.undefinedType Bindings.empty depth).map
          Prod.fst) = ([], [numeral 12]) := by
  decide +kernel

/-- The checked service suspends that shallow request without issuing a
no-result reply; the C caller remains waiting for its retained computation. -/
theorem shallow_budget_suspends_request :
    let initial := Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Configuration.initial space
      (.atom (callAtom "grow" [numeral 2, numeral 7]) Atom.undefinedType Bindings.empty 64)
    let run := mettaService.run 6000 initial
    (run.1.length, match run.2 with | .suspended _ _ => true | _ => false) = (0, true) := by
  decide +kernel

/-- `int main(void) { int x; x = coin(); return x; }` -/
def coinUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "x"],
                      .node "Call" [.node "Var" [.text "coin"], .node "NoArguments" []]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "x"]]]]]]]]]]]

/-- Both MeTTa results are published; no result is chosen, and the program stops
with the fault of the service. -/
theorem two_metta_results_stop_the_program :
    (runComposed coinUnit 400).map (fun run => (stoppedWith run, mettaResults run.1, failedReplies run.1)) =
      some (some (.service "coin"), [zeroAtom, succAtom zeroAtom], ([.several 2], 1)) := by
  decide +kernel

/-- `int main(void) { int x; x = stuck(); return x; }` -/
def stuckUnit : CanonicalTerm :=
  .node "TranslationUnit" [
    .seq [
      .node "ExternalFunction" [
        .node "FunctionDefinition" [
          .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
          .node "Declarator" [
            .node "FunctionDeclarator" [
              .node "NameDeclarator" [.text "main"],
              .node "ParameterTypes" [
                .seq [
                  .node "AbstractParameter" [
                    .node "UniqueDeclarationSpecifiers" [.node "Void" [], .seq []],
                    .node "NoAbstractDeclarator" []]]]]],
          .seq [],
          .node "Block" [
            .seq [
              .node "BlockDeclaration" [
                .node "Declaration" [
                  .node "PrimitiveDeclarationSpecifiers" [.node "Int" [], .seq []],
                  .node "InitDeclarators" [
                    .seq [.node "InitDeclarator" [.node "Declarator" [.node "NameDeclarator" [.text "x"]]]]]]],
              .node "BlockStatement" [
                .node "ExpressionStatement" [
                  .node "SomeFullExpression" [
                    .node "Assign" [
                      .node "Var" [.text "x"],
                      .node "Call" [.node "Var" [.text "stuck"], .node "NoArguments" []]]]]],
              .node "BlockStatement" [
                .node "JumpStatement" [.node "Return" [.node "SomeFullExpression" [.node "Var" [.text "x"]]]]]]]]]]]

/-- `stuck` has no equation, so MeTTa returns the call itself, which is not a numeral. -/
theorem unreadable_metta_result_stops_the_program :
    (runComposed stuckUnit 400).map (fun run => (stoppedWith run, failedReplies run.1)) =
      some (some (.service "stuck"), ([.unreadable (callAtom "stuck" [])], 1)) := by
  decide +kernel

/-- The same C loop and request codec run through the scoped HE service. -/
theorem scoped_metta_served_loop_returns_nine :
    (runComposed servicesUnit 5000 scopedMettaService).map (fun run =>
      (returnedValue run,calls run.1,mettaResults run.1)) =
      some (some 9,3,[numeral 3,numeral 6,numeral 9]) := by
  decide +kernel

/-- The scoped service preserves both alternatives instead of choosing one
to satisfy the C function's single-return contract. -/
theorem two_scoped_metta_results_stop_the_program :
    (runComposed coinUnit 800 scopedMettaService).map (fun run =>
      (stoppedWith run,mettaResults run.1,failedReplies run.1)) =
      some (some (.service "coin"),[zeroAtom,succAtom zeroAtom],([.several 2],1)) := by
  decide +kernel

end Mettapedia.Languages.C11.FixedCoreServiceControls
