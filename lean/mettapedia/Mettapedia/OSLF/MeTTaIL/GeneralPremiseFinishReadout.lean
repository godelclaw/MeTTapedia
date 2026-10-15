import Mettapedia.OSLF.MeTTaIL.GeneralPremiseExecutionCoverage
import Mettapedia.OSLF.Framework.GeneralFiniteWorkReadout

/-!
# Exact readouts of the terminating premise search

The actual continuation tree determines the complete ordered answer and
obligation histories. Its finite work account drains the executable machine.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution

theorem finish_readouts (environment : Environment) (goal : Goal) :
    (finish environment goal).answers = (treeStart environment goal).answers ∧
      (finish environment goal).unresolved = (treeStart environment goal).obligations := by
  have checked := Scheduler.finiteWork_readouts (expand environment goal)
    (treeStart environment goal).cost (start environment goal)
    (.cons (treeStart environment goal) .nil)
    (by simp only [Scheduler.TaskForest.cost, Nat.add_zero, Nat.le_refl])
  simpa only [finish, start, run, Scheduler.TaskForest.answers, Scheduler.TaskForest.obligations,
    List.append_nil, List.nil_append] using checked

theorem finish_answers (environment : Environment) (goal : Goal) :
    (finish environment goal).answers = (treeStart environment goal).answers :=
  (finish_readouts environment goal).1

theorem finish_obligations (environment : Environment) (goal : Goal) :
    (finish environment goal).unresolved = (treeStart environment goal).obligations :=
  (finish_readouts environment goal).2

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Execution
