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
          match dispatchBaseStep [sourceClause] state with
          | some (.next next none) =>
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
          match dispatchBaseStep [] state with
          | some (.next next none) =>
              match next.control.current, next.choices with
              | [.fail], [_] => true
              | _, _ => false
          | _ => false
      | _ => false

#guard sharedUnifyThenCutMaterializes
#guard typedClauseUsesCanonicalEntry
#guard typedClauseUsesSharedSelectStep
#guard typedBodyUsesSharedUnifyingStep
#guard typedCallUsesSharedDispatch
#guard typedCutRetainsCallerChoice

end Mettapedia.Logic.Prolog.RuntimeControlRegression
