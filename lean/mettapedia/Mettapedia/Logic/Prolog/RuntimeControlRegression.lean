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

#guard sharedUnifyThenCutMaterializes
#guard typedClauseUsesCanonicalEntry

end Mettapedia.Logic.Prolog.RuntimeControlRegression
