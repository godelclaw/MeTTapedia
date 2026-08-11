import Mettapedia.Logic.Prolog.SourceSignature
import Mettapedia.Logic.Prolog.RuntimeControl

/-!
# Concrete callable decoding for Prolog source terms

This module gives the concrete source signature a read-only realization of
`call/N`.  It is not a resolver or a second dispatch loop: `RuntimeQuery`
invokes this decoder from its single phase transition and installs the
predicate-like cut boundary.  The decoder only interprets an existing heap
graph as typed `RuntimeGoal` instructions.

The callable spine follows SWI-Prolog V10.1.9 `i_metacall_common` in
`src/pl-vmi.c`: an atom supplies a predicate name, a compound supplies its
functor and existing arguments, and `call/N` appends the extra arguments.
With no extra arguments, the standard control functors are decoded back into
the same typed control constructors produced by the source reader.
-/

namespace Mettapedia.Logic.Prolog.SourceRuntime

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize
open SourceSignature RuntimeControl

abbrev Sigma := SourceSignature.signature
abbrev State := RuntimeControl.State Sigma
abbrev Session := RuntimeControl.Session Sigma

/-- SWI-Prolog's ISO instantiation-error term for `throw/1`, including the
predicate context reported by version 10.1.9. -/
def throwInstantiationErrorTerm : SourceSignature.Term :=
  compound "error" [
    atom "instantiation_error",
    compound "context" [
      compound ":" [atom "system", compound "/" [atom "throw", integer 1]],
      var "_" 0
    ]
  ]

/-- Language-owned packet content for an unbound throw root.  `RuntimeQuery`
detects that root and owns every raise, match, unwind, and recovery
transition. -/
def throwInstantiationError : LP.RuntimeException.Packet Sigma := {
  term := LP.Term.atScope 0 throwInstantiationErrorTerm
}

@[simp]
theorem throwInstantiationError_term :
    throwInstantiationError.term =
      LP.Term.atScope 0 throwInstantiationErrorTerm := rfl

/-- The exact function-symbol to relation-symbol bridge used by ordinary
callable compounds.  Extra `call/N` arguments extend, rather than replace,
the compound's existing arity. -/
def predicateOfCompound (symbol : CompoundIndicator) (extraArity : Nat) :
    PredicateIndicator := {
  name := symbol.name
  arity := symbol.arity + extraArity
}

@[simp]
theorem predicateOfCompound_arity (symbol : CompoundIndicator)
    (extraArity : Nat) :
    (predicateOfCompound symbol extraArity).arity =
      symbol.arity + extraArity := rfl

private def ordinaryCall (name : String) (arguments : List Addr) :
    RuntimeGoal Sigma.scoped :=
  .call {
    symbol := { name, arity := arguments.length }
    args := arguments.toArray
  }

private def compoundCall (symbol : CompoundIndicator)
    (arguments extraArgs : List Addr) : RuntimeGoal Sigma.scoped :=
  .call {
    symbol := predicateOfCompound symbol extraArgs.length
    args := (arguments ++ extraArgs).toArray
  }

/-- Dereference one callable root without exposing trail/checkpoint authority
to the decoder. -/
private def dereferencedCell (heap : Heap Sigma.scoped) (address : Addr) :
    Except LP.RuntimeQuery.QueryError (Cell Sigma.scoped) :=
  match heap.deref address with
  | .error error => .error (.memory error)
  | .ok (.variableCycle cycle) =>
      .error (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match heap[root]? with
      | none => .error (.memory (.invalidAddress root))
      | some cell => .ok cell

/-- Bounded decoding of one finite callable graph.  Rational cycles are not
silently unfolded; exhausting the heap-sized bound fails closed until the
runtime exception channel can expose the corresponding ISO error term. -/
def decodeCallableAux : Nat → Heap Sigma.scoped → Addr → List Addr →
    Except LP.RuntimeQuery.QueryError (List (RuntimeGoal Sigma.scoped))
  | 0, _, _, _ => .error .unsupportedInstruction
  | fuel + 1, heap, address, extraArgs => do
      let cell ← dereferencedCell heap address
      match cell with
      | .var _ none => .error .unsupportedInstruction
      | .var _ (some _) => .error .unsupportedInstruction
      | .const (.atom name) =>
          if extraArgs.isEmpty then
            match name with
            | "true" => pure []
            | "fail" => pure [.fail]
            | "!" => pure [.cut]
            | _ => pure [ordinaryCall name []]
          else
            pure [ordinaryCall name extraArgs]
      | .const _ => .error .unsupportedInstruction
      | .app symbol arguments =>
          let arguments := arguments.toList
          if arguments.length != symbol.arity then
            .error (.memory .illFormedHeap)
          else if !extraArgs.isEmpty then
            pure [compoundCall symbol arguments extraArgs]
          else
            match symbol.name, arguments with
            | ",", [left, right] => do
                let decodedLeft ← decodeCallableAux fuel heap left []
                let decodedRight ← decodeCallableAux fuel heap right []
                pure (decodedLeft ++ decodedRight)
            | ";", [choice, elseBranch] => do
                let choiceCell ← dereferencedCell heap choice
                match choiceCell with
                | .app choiceSymbol choiceArguments =>
                    match choiceSymbol.name, choiceArguments.toList with
                    | "->", [condition, thenBranch] => do
                        let decodedCondition ←
                          decodeCallableAux fuel heap condition []
                        let decodedThen ←
                          decodeCallableAux fuel heap thenBranch []
                        let decodedElse ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.ifThenElse decodedCondition decodedThen decodedElse]
                    | "*->", [condition, thenBranch] => do
                        let decodedCondition ←
                          decodeCallableAux fuel heap condition []
                        let decodedThen ←
                          decodeCallableAux fuel heap thenBranch []
                        let decodedElse ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.softIfThenElse decodedCondition decodedThen
                          decodedElse]
                    | _, _ => do
                        let decodedLeft ← decodeCallableAux fuel heap choice []
                        let decodedRight ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.disj decodedLeft decodedRight]
                | _ => do
                    let decodedLeft ← decodeCallableAux fuel heap choice []
                    let decodedRight ← decodeCallableAux fuel heap elseBranch []
                    pure [.disj decodedLeft decodedRight]
            | "->", [condition, thenBranch] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedThen ← decodeCallableAux fuel heap thenBranch []
                pure [.ifThenElse decodedCondition decodedThen [.fail]]
            | "*->", [condition, thenBranch] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedThen ← decodeCallableAux fuel heap thenBranch []
                pure [.softIfThenElse decodedCondition decodedThen [.fail]]
            | "once", [goal] => do
                let decoded ← decodeCallableAux fuel heap goal []
                pure [.once decoded]
            | "\\+", [goal] => do
                let decoded ← decodeCallableAux fuel heap goal []
                pure [.neg decoded]
            | "=", [left, right] => pure [.unify left right]
            | "\\=", [left, right] => pure [.notUnify left right]
            | "var", [term] => pure [.isVar term]
            | "findall", [template, generator, bag] => do
                let decodedGenerator ← decodeCallableAux fuel heap generator []
                pure [.findall template decodedGenerator bag]
            | "catch", [guarded, catcher, recovery] => do
                let decodedGuarded ← decodeCallableAux fuel heap guarded []
                let decodedRecovery ← decodeCallableAux fuel heap recovery []
                pure [.catch decodedGuarded catcher decodedRecovery]
            | "throw", [ball] => pure [.throw ball]
            | _, _ => pure [compoundCall symbol arguments []]

/-- Decode one callable at the current heap high-water. -/
def decodeCallable (heap : Heap Sigma.scoped) (address : Addr)
    (extraArgs : List Addr) :
    Except LP.RuntimeQuery.QueryError (List (RuntimeGoal Sigma.scoped)) :=
  decodeCallableAux (heap.size + 1) heap address extraArgs

/-- Recognize `call/N` without inspecting the heap.  The classifier exposes
only the first argument and ordered extra arguments; the shared engine invokes
`decodeCallable` afterwards. -/
def metaCall? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × List Addr) :=
  if goal.symbol.name = "call" then
    match goal.args.toList with
    | callable :: extraArgs =>
        if goal.symbol.arity = extraArgs.length + 1 then
          some (callable, extraArgs)
        else none
    | [] => none
  else none

def services : RuntimeControl.Services Sigma where
  metaCall? := metaCall?
  decoder := { decode := decodeCallable }
  unboundThrowError := some throwInstantiationError

@[simp]
theorem services_unboundThrowError :
    services.unboundThrowError = some throwInstantiationError := rfl

/-- Execute concrete source terms through the one shared runtime with
callable decoding enabled. -/
def step (program : SourceSignature.Program) (state : State) :
    RuntimeControl.StepResult Sigma :=
  RuntimeControl.stepWith services program state

def pull (program : SourceSignature.Program) : Nat → State →
    RuntimeControl.PullResult Sigma :=
  RuntimeControl.pullWith services program

def openSession (memory : Memory Sigma.scoped) (queryScope nextScope : Nat)
    (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  RuntimeControl.openSessionWith services memory queryScope nextScope program goal

def openEmpty (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  openSession (Memory.empty Sigma.scoped) 0 1 program goal

/-- Session resumption delegates to `RuntimeControl.pullSession`; the stored
service selects `pullCoreWithMeta` inside the same canonical phase loop. -/
def pullSession (fuel : Nat) (session : Session) :
    RuntimeControl.SessionPullResult Sigma :=
  RuntimeControl.pullSession fuel session

end Mettapedia.Logic.Prolog.SourceRuntime
