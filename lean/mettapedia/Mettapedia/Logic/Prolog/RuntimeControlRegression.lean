import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.LP.RuntimeClauseEntry
import Mettapedia.Logic.LP.RuntimeQueryRegression

/-!
# Runtime-control materialization regressions

The fixture below checks two load-bearing properties at once: canonical source
variables retain sharing in the LP heap, and source-level cut remains a typed
control instruction rather than becoming an ordinary runtime atom.
-/

namespace Mettapedia.Logic.Prolog.RuntimeControlRegression

open Mettapedia.Logic
open LP.RuntimeTerm
open LP.RuntimeQueryRegression
open RuntimeControl

def sharedUnifyThenCut : Goal qSig :=
  .conj (.unify (.var .x) (.var .x)) .cut

def sharedUnifyThenCutMaterializes : Bool :=
  match materializeGoal (Memory.empty qSig) sharedUnifyThenCut with
  | .error _ => false
  | .ok result =>
      match result.goals with
      | [.unify left right, .cut] =>
          left == right && result.memory.heap.size == 1 &&
            result.memory.trail.size == 0
      | _ => false

/-- A typed Prolog body enters through the same head-unification mechanism as
an LP clause.  The source query and clause are standardized into distinct
scopes before they share one heap. -/
def typedClauseUsesCanonicalEntry : Bool :=
  let sourceQuery : Goal qSig := .call (unary .choose (.const .a))
  let sourceClause : Clause qSig := {
    head := unary .choose (.var .x)
    body := .cut
  }
  match materializeGoal (Memory.empty qSig.scoped)
      (sourceQuery.atScope 0) with
  | .error _ => false
  | .ok queryResult =>
      match queryResult.goals with
      | [.call goal] =>
          match materializeClause queryResult.memory
              (sourceClause.atScope 1) with
          | .error _ => false
          | .ok clauseResult =>
              match LP.RuntimeClauseEntry.enter goal clauseResult.clause.head
                  clauseResult.memory clauseResult.clause.body with
              | .error _ => false
              | .ok entered =>
                  match entered.body,
                      LP.RuntimeUnification.runSteps 16 entered.unifier with
                  | [.cut], .terminal (.success _) => true
                  | _, _ => false
      | _ => false

/-- The actual shared selected-clause transition accepts a typed Prolog
clause.  It advances the persistent scope, enters the canonical unifier, and
retains the typed body without acquiring any Prolog-specific search state. -/
def typedClauseUsesSharedSelectStep : Bool :=
  let sourceQuery : Goal qSig := .call (unary .choose (.const .a))
  let sourceClause : Clause qSig := {
    head := unary .choose (.var .x)
    body := .cut
  }
  match materializeGoal (Memory.empty qSig.scoped)
      (sourceQuery.atScope 0) with
  | .error _ => false
  | .ok queryResult =>
      match queryResult.goals with
      | [.call goal] =>
          let cursor : LP.RuntimeQuery.ClauseCursorCore qSig
              (RuntimeGoal qSig.scoped) (Clause qSig) := {
            checkpoint := queryResult.memory.checkpoint
            goal
            clauses := [sourceClause]
            cutDepth := 0
            frames := []
          }
          let state : LP.RuntimeQuery.StateCore qSig
              (RuntimeGoal qSig.scoped) (Clause qSig) := {
            memory := queryResult.memory
            control := { current := [], cutDepth := 0, frames := [] }
            choices := []
            queryCheckpoint := (Memory.empty qSig.scoped).checkpoint
            queryVarMap := queryResult.varMap
            nextScope := 1
            phase := .select cursor
          }
          match LP.RuntimeQuery.selectStep clauseMaterializer state cursor with
          | .terminal _ => false
          | .next next _ =>
              match next.phase with
              | .unifying attempt machine =>
                  match attempt.body, LP.RuntimeUnification.runSteps 16 machine with
                  | [.cut], .terminal (.success _) => next.nextScope == 2
                  | _, _ => false
              | _ => false
      | _ => false

/-- The shared unifier-success transition installs the typed Prolog body in
the canonical query control state.  In particular, the transition cannot
reinterpret `cut` as an LP atom or discard it at the control seam. -/
def typedBodyUsesSharedUnifyingStep : Bool :=
  let sourceQuery : Goal qSig := .call (unary .choose (.const .a))
  let sourceClause : Clause qSig := {
    head := unary .choose (.var .x)
    body := .cut
  }
  match materializeGoal (Memory.empty qSig.scoped)
      (sourceQuery.atScope 0) with
  | .error _ => false
  | .ok queryResult =>
      match queryResult.goals with
      | [.call goal] =>
          let cursor : LP.RuntimeQuery.ClauseCursorCore qSig
              (RuntimeGoal qSig.scoped) (Clause qSig) := {
            checkpoint := queryResult.memory.checkpoint
            goal
            clauses := [sourceClause]
            cutDepth := 0
            frames := []
          }
          let state : LP.RuntimeQuery.StateCore qSig
              (RuntimeGoal qSig.scoped) (Clause qSig) := {
            memory := queryResult.memory
            control := { current := [], cutDepth := 0, frames := [] }
            choices := []
            queryCheckpoint := (Memory.empty qSig.scoped).checkpoint
            queryVarMap := queryResult.varMap
            nextScope := 1
            phase := .select cursor
          }
          match LP.RuntimeQuery.selectStep clauseMaterializer state cursor with
          | .terminal _ => false
          | .next selected _ =>
              match selected.phase with
              | .unifying attempt machine =>
                  match LP.RuntimeUnification.runSteps 16 machine with
                  | .terminal (.success memory) =>
                      match LP.RuntimeQuery.unifyingStep selected attempt
                          (.terminal (.success memory)) with
                      | .next installed none =>
                          match installed.phase, installed.control.current with
                          | .dispatch, [.cut] => installed.nextScope == 2
                          | _, _ => false
                      | _ => false
                  | _ => false
              | _ => false
      | _ => false

/-- Typed call classification transfers the real source clause list into a
shared cursor and records the caller continuation in the canonical frame. -/
def typedCallUsesSharedDispatch : Bool :=
  let sourceQuery : Goal qSig := .call (unary .choose (.const .a))
  let sourceClause : Clause qSig := {
    head := unary .choose (.var .x)
    body := .cut
  }
  match materializeGoal (Memory.empty qSig.scoped)
      (sourceQuery.atScope 0) with
  | .error _ => false
  | .ok queryResult =>
      match queryResult.goals with
      | [.call goal] =>
          let state : LP.RuntimeQuery.StateCore qSig
              (RuntimeGoal qSig.scoped) (Clause qSig) := {
            memory := queryResult.memory
            control := {
              current := [.call goal, .fail]
              cutDepth := 0
              frames := []
            }
            choices := []
            queryCheckpoint := (Memory.empty qSig.scoped).checkpoint
            queryVarMap := queryResult.varMap
            nextScope := 1
            phase := .dispatch
          }
          match step [sourceClause] state with
          | .next next none =>
              match next.phase with
              | .select cursor =>
                  match cursor.clauses, cursor.frames with
                  | [_], [frame] =>
                      cursor.cutDepth == 0 &&
                        match frame.continuation with
                        | [.fail] => true
                        | _ => false
                  | _, _ => false
              | _ => false
          | _ => false
      | _ => false

/-- A typed cut at nonzero depth keeps the caller's older cursor.  This is the
non-degenerate pruning arm: replacing `retainBottom` with `[]` fails. -/
def typedCutRetainsCallerChoice : Bool :=
  let sourceQuery : Goal qSig := .call (unary .choose (.const .a))
  let sourceClause : Clause qSig := {
    head := unary .choose (.var .x)
    body := .cut
  }
  match materializeGoal (Memory.empty qSig.scoped)
      (sourceQuery.atScope 0) with
  | .error _ => false
  | .ok queryResult =>
      match queryResult.goals with
      | [.call goal] =>
          let older : LP.RuntimeQuery.ClauseCursorCore qSig
              (RuntimeGoal qSig.scoped) (Clause qSig) := {
            checkpoint := queryResult.memory.checkpoint
            goal
            clauses := [sourceClause]
            cutDepth := 0
            frames := []
          }
          let state : LP.RuntimeQuery.StateCore qSig
              (RuntimeGoal qSig.scoped) (Clause qSig) := {
            memory := queryResult.memory
            control := {
              current := [.cut, .fail]
              cutDepth := 1
              frames := []
            }
            choices := [older]
            queryCheckpoint := (Memory.empty qSig.scoped).checkpoint
            queryVarMap := queryResult.varMap
            nextScope := 1
            phase := .dispatch
          }
          match step [] state with
          | .next next none =>
              match next.control.current, next.choices with
              | [.fail], [_] => true
              | _, _ => false
          | _ => false
      | _ => false

/-- Unimplemented structured control is a typed runtime error, never Prolog
failure, success, or an erased instruction. -/
def structuredControlIsExplicitlyUnsupported : Bool :=
  let memory := Memory.empty qSig.scoped
  let state : State qSig := {
    memory
    control := {
      current := [.disj [] []]
      cutDepth := 0
      frames := []
    }
    choices := []
    queryCheckpoint := memory.checkpoint
    queryVarMap := []
    nextScope := 1
    phase := .dispatch
  }
  match step [] state with
  | .terminal (.runtimeError .unsupportedInstruction restored) =>
      restored.heap.isEmpty && restored.trail.isEmpty
  | _ => false

/-- A source conjunction containing real typed cut enters through the shared
query opener with one checkpoint, no alternatives, and the exact flattened
instruction order. -/
def typedGoalUsesSharedOpenQuery : Bool :=
  let source : Goal qSig :=
    .conj (.call (unary .choose (.const .a))) .cut
  match openQuery (Memory.empty qSig.scoped) 0 1 source with
  | .error _ => false
  | .ok state =>
      match state.phase, state.control.current, state.choices,
          state.control.frames with
      | .dispatch, [.call _, .cut], [], [] =>
          state.control.cutDepth == 0 && state.nextScope == 1
      | _, _, _, _ => false

/-- Collect typed-session answers while treating an open fuel boundary or
runtime error as a failed regression, never as completion. -/
def collectTyped (answerBudget : Nat) (session : Session qSig) :
    Option (List QConst × Nat × Nat) :=
  match answerBudget with
  | 0 => none
  | answerBudget + 1 =>
      match pullSession 64 session with
      | .open _ => none
      | .terminal (.runtimeError _ _) => none
      | .terminal (.completed memory) =>
          some ([], memory.heap.size, memory.trail.size)
      | .answer answer next =>
          match answerConstant? answer, collectTyped answerBudget next with
          | some symbol, some (symbols, heapSize, trailSize) =>
              some (symbol :: symbols, heapSize, trailSize)
          | _, _ => none

/-- End-to-end typed execution uses source clauses with typed cut, the shared
opener, phase loop, cursor, graph unifier, pull loop, and cleanup.  The first
clause commits and prunes the later `choose(b)` clause. -/
def typedCutSessionRun : Option (List QConst × Nat × Nat) :=
  let typedProgram : Program qSig := [
    { head := unary .choose (.const .a), body := .cut },
    { head := unary .choose (.const .b), body := .succeed }
  ]
  let query : Goal qSig := .call (unary .choose (.var .x))
  match openEmpty typedProgram query with
  | .error _ => none
  | .ok session => collectTyped 3 session

/-- Execute one typed source goal from an isolated empty session. -/
def runTyped (program : Program qSig) (goal : Goal qSig) :
    Option (List QConst × Nat × Nat) :=
  match openEmpty program goal with
  | .error _ => none
  | .ok session => collectTyped 3 session

def inlineUnifySuccess : Goal qSig :=
  .unify (.var .x) (.const .a)

def inlineUnifyFailureAfterBinding : Goal qSig :=
  .conj (.unify (.var .x) (.const .a))
    (.unify (.var .x) (.const .b))

def isVarBeforeBinding : Goal qSig :=
  .conj (.isVar (.var .x))
    (.unify (.var .x) (.const .a))

def isVarAfterBinding : Goal qSig :=
  .conj (.unify (.var .x) (.const .a))
    (.isVar (.var .x))

#guard sharedUnifyThenCutMaterializes
#guard typedClauseUsesCanonicalEntry
#guard typedClauseUsesSharedSelectStep
#guard typedBodyUsesSharedUnifyingStep
#guard typedCallUsesSharedDispatch
#guard typedCutRetainsCallerChoice
#guard structuredControlIsExplicitlyUnsupported
#guard typedGoalUsesSharedOpenQuery
#guard typedCutSessionRun == some ([.a], 0, 0)
#guard runTyped [] inlineUnifySuccess == some ([.a], 0, 0)
#guard runTyped [] inlineUnifyFailureAfterBinding == some ([], 0, 0)
#guard runTyped [] isVarBeforeBinding == some ([.a], 0, 0)
#guard runTyped [] isVarAfterBinding == some ([], 0, 0)

end Mettapedia.Logic.Prolog.RuntimeControlRegression
