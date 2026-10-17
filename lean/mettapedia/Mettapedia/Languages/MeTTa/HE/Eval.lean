import Mettapedia.Languages.MeTTa.HE.TypeCheck
import Mettapedia.Languages.MeTTa.HE.ArgumentResult
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Finite evaluation with the all-candidate type-selection policy

This executable profile visits every applicable function type and every
successful type-binding path. That all-candidate policy can repeat answers and
is not Rust HE's first flattened success selection. The retained
`FirstSuccessRecursiveStrategy` supplies that selection policy using the same
requests, invocation dispatcher, and continuations.

The typed evaluator and raw minimal invocation share one dispatcher. Finite
allowances bound recursive evaluation and leaf operations; an empty finite
approximation is not completed failure. The retained checked machine guards
those boundaries and saves its full pending continuation.

The independent source comparison is proved downstream. The executable
read-only grounded profile supplies emitted replies; completed native values
need explicit producer provenance. Opaque context, native-call and serialized
binding services remain named frontiers of the checked worker. Whole-operand
invocation-entry materialization is separate from this ready-input dispatcher.

## Equation instances
Every function carries the atoms that the computation around it still holds
(`live`): pending arguments, the operator type, the call's own result type and
already evaluated heads. An equation call renames its rule apart from those atoms,
the call itself, its type and its bindings (`equationScope`), so a rule instance
never reuses a variable that is visible at the call. Nested and recursive calls
of one equation, such as `(inc (inc Z))`, therefore keep both instances' bindings,
and separate calls of one rule get separate copies of its right-hand-side-only
variables, as in Hyperon Experimental.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type.Presentation.BindingTheory (aliasConstraints)

/-- Extract child elements from an atom: expressions unwrap, others wrap in singleton. -/
def atomElements : Atom → List Atom
  | .expression es => es
  | a => [a]

/-- Ordinary calls consume a producer's reply before considering another
recursive evaluation. A refusal restores the original post-argument call;
stopped replies remain data. Primitive minimal operations have their own raw
return policy and do not use this boundary. -/
def ordinaryCallReturn (original value : Atom) (bindings : Bindings)
    (evaluate : Atom → Bindings → ResultSet) : ResultSet :=
  if value == Atom.notReducible then [(original, bindings)]
  else if isEmptyOrError value then [(value, bindings)]
  else evaluate value bindings

@[simp] theorem ordinaryCallReturn_notReducible (original : Atom) (bindings : Bindings)
    (evaluate : Atom → Bindings → ResultSet) :
    ordinaryCallReturn original Atom.notReducible bindings evaluate = [(original, bindings)] := by
  simp [ordinaryCallReturn]

theorem ordinaryCallReturn_evaluate (original value : Atom) (bindings : Bindings)
    (evaluate : Atom → Bindings → ResultSet) (accepted : value ≠ Atom.notReducible)
    (running : isEmptyOrError value = false) :
    ordinaryCallReturn original value bindings evaluate = evaluate value bindings := by
  simp [ordinaryCallReturn, accepted, running]


/-- Raw invocation and ordinary typed completion share one dispatcher. -/
inductive InvocationMode where
  | raw
  | ordinary (expected : Atom)
  deriving Repr, DecidableEq

/-- Producer provenance is supplied by the service boundary, never by the
shape of the emitted atom. The legacy executable dispatch supplies emissions. -/
inductive InvocationProvenance where
  | emitted
  | completed
  deriving Repr, DecidableEq

def InvocationMode.expected : InvocationMode → Atom
  | .raw => Atom.undefinedType
  | .ordinary expected => expected

def InvocationMode.pendingScope (mode : InvocationMode) (live : List Atom) : List Atom :=
  match mode with
  | .raw => live
  | .ordinary expected => expected :: live

def InvocationMode.errorPassthrough (mode : InvocationMode) (value : Atom) : Bool :=
  match mode with
  | .ordinary _ => isErrorAtom value
  | .raw => false

def minimalInstruction : Atom → Bool
  | .expression (.symbol name :: _) => name ∈
      ["eval", "evalc", "chain", "unify", "cons-atom", "decons-atom", "function",
       "collapse-bind", "superpose-bind", "metta", "context-space", "call-native"]
  | _ => false

/-- This read-only executable slice has no opaque minimal host package. -/
def minimalCoreSupported : Atom → Bool
  | .expression [.symbol "eval", _] => true
  | .expression [.symbol "chain", _, .var _, _] => true
  | .expression (.symbol "unify" :: _) => true
  | .expression [.symbol "cons-atom", _, .expression _] => true
  | .expression [.symbol "decons-atom", .expression (_ :: _)] => true
  | .expression [.symbol "function", .expression _] => true
  | _ => false

def chainSubstitute (name : String) (replacement template : Atom) : Atom :=
  SubstitutionAlgebra.subst (fun key => if key = name then some replacement else none) template

def functionTerminal (caller : Option Atom) (terminal : Atom) : Atom :=
  match terminal with
  | .expression [.symbol "return", value] => value
  | _ => Atom.error (caller.getD terminal) (.symbol "NoReturn")

/-- Exact query occurrences are traversed in their stored order. Refusal is
chosen only after this whole merge/filter stage has produced no candidate. -/
def rawQueryResults (space : Space) (value expected : Atom) (incoming : Bindings)
    (depth : Nat) (live : List Atom) : ResultSet :=
  (queryEquationsAvoiding (equationScope live value expected incoming) space value depth).flatMap
    fun (rhs, selected) => (mergeBindings selected (aliasConstraints incoming) depth).filterMap fun merged =>
      if merged.hasLoop then none else some (merged.applyFull rhs depth, merged)

/-- Completed service values use the declared demand, without reactivating
call-looking syntax. -/
def completedCallReturn (space : Space) (value expected : Atom) (bindings : Bindings)
    (depth : Nat) (lookup : TypeLookup := rawTypeLookup space) : ResultSet :=
  if isEmptyOrError value || expected == Atom.undefinedType || expected == Atom.atomType ||
      expected == getMetaType value || getMetaType value == Atom.variableType then
    [(value, bindings)]
  else typeCast value expected space bindings depth lookup

mutual

/-- Evaluate an atom to an ordered result set at the selected finite depth. -/
def evalAtom (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) (live : List Atom := []) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    if isEmptyOrError atom then
      [(atom, b)]
    else if type_ == Atom.atomType
         || type_ == getMetaType atom
         || getMetaType atom == Atom.variableType then
      [(atom, b)]
    else if getMetaType atom == Atom.symbolType
         || getMetaType atom == Atom.groundedType
         || atom == Atom.unit then
      typeCast atom type_ space b n
    else if getMetaType atom == Atom.expressionType then
      let results := interpretExpression space dispatch atom type_ b n live
      let successes := results.filter fun (r, _) => !isErrorAtom r
      if !successes.isEmpty then successes
      else results.filter fun (r, _) => isErrorAtom r
    else [(atom, b)]

/-- Interpret an expression through its function or tuple path. This finite
worker accumulates applicable type entries. First-success source admission is
a separate downstream obligation; syntax dispatch alone does not prove it. -/
def interpretExpression (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (fuel : Nat) (live : List Atom := []) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match atom with
    | .expression (op :: _) =>
      let types := getAtomTypes space op
      let funcResults : ResultSet := types.flatMap fun funcType =>
        if isFunctionType funcType then
          match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
          | .inr succs =>
            succs.flatMap fun b' =>
              let retType :=
                if getFunctionRetType funcType == some Atom.expressionType
                then Atom.undefinedType
                else (getFunctionRetType funcType).getD Atom.undefinedType
              let interpResults := interpretFunction space dispatch atom funcType b' n (retType :: live)
              interpResults.flatMap fun (r, rb) =>
                invoke space dispatch (.ordinary retType) r rb n live
          | .inl _ => []
        else []
      let hasNonFunc := types.any fun t =>
        !isFunctionType t || t == Atom.undefinedType
      let tupleResults : ResultSet :=
        if hasNonFunc then
          let interpResults := interpretTuple space dispatch atom b n (type_ :: live)
          interpResults.flatMap fun (r, rb) =>
            invoke space dispatch (.ordinary type_) r rb n live
        else []
      let allResults := funcResults ++ tupleResults
      if !allResults.isEmpty then allResults
      else if !hasNonFunc then
        let allChecksFailed := types.all fun funcType =>
          if isFunctionType funcType then
            match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
            | .inl _ => true
            | .inr _ => false
          else true
        if allChecksFailed then
          types.flatMap fun funcType =>
            if isFunctionType funcType then
              match checkIfFunctionTypeIsApplicable atom funcType type_ space b n with
              | .inl errs => errs.map fun e => (e, b)
              | .inr _ => []
            else []
        else []
      else []
    | _ => []

/-- Interpret a function call (evaluate head, then args). -/
def interpretFunction (space : Space) (dispatch : GroundedDispatch)
    (atom opType : Atom) (b : Bindings) (fuel : Nat) (live : List Atom := []) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match atom with
    | .expression (op :: args) =>
      let headResults := evalAtom space dispatch op opType b n (opType :: args ++ live)
      headResults.flatMap fun (headR, headB) =>
        if isEmptyOrError headR then [(headR, headB)]
        else
          match getFunctionArgTypes opType with
          | some argTypes =>
            let tailResults := interpretArgs space dispatch args argTypes headB n (headR :: live)
            tailResults.map fun (tailR, tailB) =>
              if argumentsSucceeded tailR = false then (tailR, tailB)
              else (.expression (headR :: argumentValues tailR), tailB)
          | none => []
    | _ => []

/-- Interpret argument list (recursive evaluation of each arg with its type). -/
def interpretArgs (space : Space) (dispatch : GroundedDispatch)
    (args types : List Atom) (b : Bindings) (fuel : Nat) (live : List Atom := []) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match args, types with
    | [], [] => [(argumentPacket [], b)]
    | arg :: remainingArgs, t :: remainingTypes =>
      let headResults := evalAtom space dispatch arg t b n (remainingArgs ++ remainingTypes ++ live)
      headResults.flatMap fun (headR, headB) =>
        if headR != arg && isEmptyOrError headR then [(headR, headB)]
        else
          let tailResults :=
            interpretArgs space dispatch remainingArgs remainingTypes headB n (headR :: live)
          tailResults.map fun (tailR, tailB) =>
            if argumentsSucceeded tailR = false then (tailR, tailB)
            else (argumentPacket (headR :: argumentValues tailR), tailB)
    | _, _ => []

/-- Interpret a tuple (recursive element-wise evaluation). -/
def interpretTuple (space : Space) (dispatch : GroundedDispatch)
    (atom : Atom) (b : Bindings) (fuel : Nat) (live : List Atom := []) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    match atom with
    | .expression [] => [(Atom.unit, b)]
    | .expression [single] =>
      (evalAtom space dispatch single Atom.undefinedType b n live).map tupleSingleton
    | .expression (hd :: hd2 :: rest) =>
      let headResults :=
        evalAtom space dispatch hd Atom.undefinedType b n (.expression (hd2 :: rest) :: live)
      headResults.flatMap fun (headR, headB) =>
        if isEmptyOrError headR then [(headR, headB)]
        else
          let tailResults :=
            interpretTuple space dispatch (.expression (hd2 :: rest)) headB n (headR :: live)
          tailResults.map fun (tailR, tailB) =>
            if isEmptyOrError tailR then (tailR, tailB)
            else (.expression (headR :: atomElements tailR), tailB)
    | _ => []

/-- One ready-input invocation dispatcher selects host, embedded instruction
or the actual equation table. Typed return is a separate continuation of the
produced reply. The caller supplies the operand at this boundary. -/
def invoke (space : Space) (dispatch : GroundedDispatch) (mode : InvocationMode)
    (atom : Atom) (b : Bindings) (fuel : Nat) (live : List Atom := [])
    (caller : Option Atom := none) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    if mode.errorPassthrough atom then [(atom, b)]
    else
      let ready := atom
      let finish := fun (value : Atom) (bindings : Bindings) =>
        match mode with
        | .raw => [(value, bindings)]
        | .ordinary expected => ordinaryCallReturn ready value bindings
            (fun value bindings => evalAtom space dispatch value expected bindings n live)
      let complete := fun (value : Atom) (bindings : Bindings) =>
        (invocationResult space dispatch value bindings n
          (mode.pendingScope live) (some ready)).flatMap fun (value, bindings) => finish value bindings
      match ready with
      | .expression (operator :: arguments) =>
        if dispatch.isExecutable operator then
          match dispatch.execute operator arguments with
          | .ok results =>
            let merged := results.flatMap fun (value, selected) =>
              (mergeBindings selected b n).map fun bindings => (bindings.applyFull value n, bindings)
            if merged.isEmpty then finish Atom.empty b
            else merged.flatMap fun (value, bindings) => complete value bindings
          | .runtimeError message => finish (Atom.error ready (.symbol message)) b
          | .noReduce | .incorrectArgument => finish Atom.notReducible b
        else if minimalInstruction ready then
          (minimalRun space dispatch ready b n (mode.pendingScope live) caller).flatMap
            fun (value, bindings) => finish value bindings
        else
          let results := rawQueryResults space ready mode.expected b n live
          if results.isEmpty then finish Atom.notReducible b
          else results.flatMap fun (value, bindings) => complete value bindings
      | _ =>
        let results := rawQueryResults space ready mode.expected b n live
        if results.isEmpty then finish Atom.notReducible b
        else results.flatMap fun (value, bindings) => complete value bindings

/-- Only an emitted function block enters a function continuation. -/
def invocationResult (space : Space) (dispatch : GroundedDispatch)
    (value : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
    (caller : Option Atom := none) (provenance : InvocationProvenance := .emitted) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 => if provenance == .completed then [(value, bindings)] else match value with
    | .expression [.symbol "function", _] =>
      minimalStep space dispatch value bindings n live caller
    | _ => [(value, bindings)]

/-- Minimal execution continues a chain's substituted template; other
instruction replies remain raw. Internal Empty is an ordinary carried value. -/
def minimalRun (space : Space) (dispatch : GroundedDispatch)
    (value : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
    (caller : Option Atom := none) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    if minimalInstruction value then
      let results := minimalStep space dispatch value bindings n live caller
      match value with
      | .expression (.symbol "chain" :: _) =>
        results.flatMap fun (value, bindings) => minimalRun space dispatch value bindings n live caller
      | _ => results
    else [(value, bindings)]

/-- One primitive instruction. Unsupported host services have no finite
approximation here; the checked worker suspends their retained request. -/
def minimalStep (space : Space) (dispatch : GroundedDispatch)
    (value : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
    (caller : Option Atom := none) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 => match value with
    | .expression [.symbol "eval", atom] =>
      invoke space dispatch .raw (bindings.applyFull atom n) bindings n live caller
    | .expression [.symbol "chain", atom, .var name, template] =>
      (minimalRun space dispatch atom bindings n (value :: live) (some value)).map
        fun (result, output) => (chainSubstitute name (output.applyFull result n) template, output)
    | .expression [.symbol "unify", target, pattern, yes, no] =>
      let results := unifySuccessResults target pattern yes bindings n
      if results.isEmpty then [(no, bindings)] else results
    | .expression (.symbol "unify" :: _) => [(mkUnifyBadArityError value, bindings)]
    | .expression [.symbol "cons-atom", head, .expression tail] =>
      [(.expression (head :: tail), bindings)]
    | .expression [.symbol "decons-atom", .expression (head :: tail)] =>
      [(.expression [head, .expression tail], bindings)]
    | .expression [.symbol "function", body@(.expression _)] =>
      (functionBody space dispatch body bindings n (value :: live) (some value)).map
        fun (terminal, output) => (functionTerminal caller terminal, output)
    | _ => []

/-- Repeated function-body execution uses each actual reached binding readout
before deciding whether its result is another instruction or a terminal. -/
def functionBody (space : Space) (dispatch : GroundedDispatch)
    (value : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := [])
    (caller : Option Atom := none) : ResultSet :=
  match fuel with
  | 0 => []
  | n + 1 =>
    (minimalRun space dispatch value bindings n live caller).flatMap fun (result, output) =>
      let materialized := output.applyFull result n
      if minimalInstruction materialized then
        functionBody space dispatch materialized output n live caller
      else [(materialized, output)]

end

/-- Ordinary invocation uses the same raw dispatcher and its typed return gate. -/
def mettaCall (space : Space) (dispatch : GroundedDispatch)
    (atom expected : Atom) (bindings : Bindings) (fuel : Nat) (live : List Atom := []) : ResultSet :=
  invoke space dispatch (.ordinary expected) atom bindings fuel live


/-- Successful primitive unification returns its materialized branch before
ordinary typed return is considered. -/
theorem minimalStep_unify_success
    {space : Space} {dispatch : GroundedDispatch}
    {target pattern yes no : Atom} {bindings : Bindings} {fuel : Nat}
    (nonempty : unifySuccessResults target pattern yes bindings fuel ≠ []) :
    minimalStep space dispatch (.expression [.symbol "unify", target, pattern, yes, no])
      bindings (fuel + 1) = unifySuccessResults target pattern yes bindings fuel := by
  cases results : unifySuccessResults target pattern yes bindings fuel with
  | nil => contradiction
  | cons head tail => simp [minimalStep, results]

theorem minimalStep_unify_no_match
    {space : Space} {dispatch : GroundedDispatch}
    {target pattern yes no : Atom} {bindings : Bindings} {fuel : Nat}
    (empty : unifySuccessResults target pattern yes bindings fuel = []) :
    minimalStep space dispatch (.expression [.symbol "unify", target, pattern, yes, no])
      bindings (fuel + 1) = [(no, bindings)] := by
  simp [minimalStep, empty]

/-- Evaluate a MeTTa atom with default settings. -/
def eval (space : Space) (atom : Atom) (fuel : Nat := 100) : ResultSet :=
  evalAtom space GroundedDispatch.none atom Atom.undefinedType Bindings.empty fuel

section Tests

example : evalAtom Space.empty GroundedDispatch.none
    Atom.empty Atom.atomType Bindings.empty 40 =
    [(Atom.empty, Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (Atom.error (.symbol "x") (.symbol "msg")) Atom.atomType Bindings.empty 40 =
    [(Atom.error (.symbol "x") (.symbol "msg"), Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (.symbol "a") Atom.atomType Bindings.empty 40 =
    [(.symbol "a", Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (.var "x") (.symbol "Int") Bindings.empty 40 =
    [(.var "x", Bindings.empty)] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    (.symbol "a") Atom.symbolType Bindings.empty 40 =
    [(.symbol "a", Bindings.empty)] := rfl

private def typedSpace := Space.ofList [
  .expression [.symbol ":", .symbol "x", .symbol "Int"]
]

private def unifyFunctionType : Atom :=
  .expression
    [.symbol "->", Atom.atomType, Atom.atomType,
      Atom.atomType, Atom.atomType, Atom.undefinedType]

private def unifyTypedSpace := Space.ofList [
  .expression [.symbol ":", .symbol "unify", unifyFunctionType]
]

example : evalAtom typedSpace GroundedDispatch.none
    (.symbol "x") (.symbol "Int") Bindings.empty 40 =
    [(.symbol "x", Bindings.empty)] := rfl

example : evalAtom typedSpace GroundedDispatch.none
    (.symbol "x") Atom.undefinedType Bindings.empty 40 =
    [(.symbol "x", Bindings.empty)] := rfl

example : mettaCall Space.empty GroundedDispatch.none
    (.expression
      [.symbol "unify",
        .expression [.symbol "A", .symbol "B"],
        .expression [.var "x", .var "y"],
        .expression [.symbol "found", .var "x", .var "y"],
        .symbol "not-found"])
    Atom.undefinedType Bindings.empty 40 =
    [(.expression [.symbol "found", .symbol "A", .symbol "B"],
      (Bindings.empty.assign "x" (.symbol "A")).assign "y" (.symbol "B"))] := rfl

example : mettaCall Space.empty GroundedDispatch.none
    (.expression
      [.symbol "unify",
        .expression [.symbol "A", .symbol "B"],
        .expression [.symbol "C", .symbol "D"],
        .symbol "success",
        .symbol "failure"])
    Atom.undefinedType Bindings.empty 40 =
    [(.symbol "failure", Bindings.empty)] := rfl

example : mettaCall Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "A", .symbol "B", .symbol "yes"])
    Atom.undefinedType Bindings.empty 40 =
    [(mkUnifyBadArityError
        (.expression [.symbol "unify", .symbol "A", .symbol "B", .symbol "yes"]),
      Bindings.empty)] := rfl

example : evalAtom unifyTypedSpace GroundedDispatch.none
    (.expression
      [.symbol "unify",
        .symbol "A",
        .symbol "A",
        .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)],
        .grounded (.int 0)])
    Atom.undefinedType Bindings.empty 60 =
    [(.expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)],
      Bindings.empty)] := rfl

example : (mettaCall Space.empty GroundedDispatch.none
    (.expression
      [.symbol "unify",
        .expression [.symbol "A", .var "b"],
        .expression [.var "a", .symbol "B"],
        .expression [.var "a", .var "b"],
        Atom.empty])
    Atom.undefinedType Bindings.empty 40).map Prod.fst =
    [.expression [.symbol "A", .symbol "B"]] := rfl

example : (mettaCall Space.empty GroundedDispatch.none
    (.expression
      [.symbol "unify",
        .expression [.symbol "A", .var "b", .symbol "C"],
        .expression [.var "a", .symbol "B", .symbol "D"],
        .expression [.var "a", .var "b"],
        Atom.empty])
    Atom.undefinedType Bindings.empty 40).map Prod.fst =
    [Atom.empty] := rfl

example : evalAtom Space.empty GroundedDispatch.none
    Atom.unit Atom.undefinedType Bindings.empty 40 =
    [(Atom.unit, Bindings.empty)] := rfl

private def eqSpace := Space.ofList [
  .expression [.symbol "=", .symbol "x", .symbol "y"]
]

example : mettaCall eqSpace GroundedDispatch.none
    (.symbol "x") Atom.undefinedType Bindings.empty 40 =
    [(.symbol "y", Bindings.empty)] := rfl

example : mettaCall Space.empty GroundedDispatch.none
    (.symbol "x") Atom.undefinedType Bindings.empty 40 =
    [(.symbol "x", Bindings.empty)] := rfl

example : mettaCall Space.empty GroundedDispatch.none
    (Atom.error (.symbol "x") (.symbol "msg")) Atom.undefinedType Bindings.empty 40 =
    [(Atom.error (.symbol "x") (.symbol "msg"), Bindings.empty)] := rfl

example : interpretArgs Space.empty GroundedDispatch.none
    [] [] Bindings.empty 40 =
    [(argumentPacket [], Bindings.empty)] := rfl

example : interpretTuple Space.empty GroundedDispatch.none
    (.expression [.symbol "a"]) Bindings.empty 40 =
    [(.expression [.symbol "a"], Bindings.empty)] := rfl

/-- A nested final argument remains one element of the outer tuple. -/
theorem eval_nested_final_tuple :
    eval Space.empty (.expression [.symbol "f", .expression [.symbol "a", .symbol "b"]]) 60 =
      [(.expression [.symbol "f", .expression [.symbol "a", .symbol "b"]], Bindings.empty)] := rfl

/-- Singleton applications do not collapse to their head. -/
theorem eval_singleton_tuple : eval Space.empty (.expression [.symbol "g"]) 40 =
    [(.expression [.symbol "g"], Bindings.empty)] := rfl

theorem eval_nested_singleton_tuple :
    eval Space.empty (.expression [.expression [.symbol "a", .symbol "b"]]) 60 =
      [(.expression [.expression [.symbol "a", .symbol "b"]], Bindings.empty)] := rfl

/-- Failure is not hidden inside a singleton success wrapper. -/
theorem interpretTuple_singleton_empty :
    interpretTuple Space.empty GroundedDispatch.none (.expression [Atom.empty]) Bindings.empty 40 =
      [(Atom.empty, Bindings.empty)] := rfl

example : eval Space.empty (.symbol "a") 10 =
    [(.symbol "a", Bindings.empty)] := rfl

private def tuplEqSpace := Space.ofList [
  .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .symbol "b"]
]

private def funcSpace := Space.ofList [
  .expression [.symbol ":", .symbol "Z", .symbol "Nat"],
  .expression [.symbol ":", .symbol "S",
    .expression [.symbol "->", .symbol "Nat", .symbol "Nat"]],
  .expression [.symbol ":", .symbol "Add",
    .expression [.symbol "->", .symbol "Nat", .symbol "Nat", .symbol "Nat"]],
  .expression [.symbol "=",
    .expression [.symbol "Add", .var "x", .symbol "Z"],
    .var "x"]
]

example : interpretTuple Space.empty GroundedDispatch.none
    (.expression [.symbol "a", .symbol "b"]) Bindings.empty 40 =
    [(.expression [.symbol "a", .symbol "b"], Bindings.empty)] := rfl

example : interpretArgs Space.empty GroundedDispatch.none
    [.symbol "a"] [Atom.undefinedType] Bindings.empty 40 =
    [(argumentPacket [.symbol "a"], Bindings.empty)] := rfl

example : interpretFunction funcSpace GroundedDispatch.none
    (.expression [.symbol "S", .symbol "Z"])
    (.expression [.symbol "->", .symbol "Nat", .symbol "Nat"])
    Bindings.empty 40 =
    [(.expression [.symbol "S", .symbol "Z"], Bindings.empty)] := rfl

example : interpretExpression Space.empty GroundedDispatch.none
    (.expression [.symbol "a", .symbol "b"]) Atom.undefinedType Bindings.empty 40 =
    [(.expression [.symbol "a", .symbol "b"], Bindings.empty)] := rfl

example : interpretExpression funcSpace GroundedDispatch.none
    (.expression [.symbol "S", .symbol "Z"]) Atom.undefinedType Bindings.empty 40 =
    [(.expression [.symbol "S", .symbol "Z"], Bindings.empty)] := rfl

example : evalAtom tuplEqSpace GroundedDispatch.none
    (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType Bindings.empty 40 =
    [(.symbol "b", Bindings.empty)] := rfl

end Tests

end Mettapedia.Languages.MeTTa.HE
