import Mettapedia.OSLF.Framework.GeneralFiniteCursorWork

/-!
# Uniqueness of actual finite scheduler work

Any finite expansion tree for a fixed task contains exactly the children of
that task's actual transition. Independent tree witnesses therefore have
identical work and readouts. Proof-only residual witnesses do not introduce
an execution policy or a chosen completion bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler

variable {Task Answer Obligation : Type}

mutual
 theorem TaskTree.unique {expand : Task → Expansion Task Answer Obligation} {task : Task}
    (first second : TaskTree expand task) : first = second :=
  match first, second with
  | .branch front, .branch back => congrArg TaskTree.branch (front.unique back)

 theorem TaskForest.unique {expand : Task → Expansion Task Answer Obligation} {tasks : List Task}
    (first second : TaskForest expand tasks) : first = second :=
  match first, second with
  | .nil, .nil => rfl
  | .cons firstHead firstTail, .cons secondHead secondTail => by
      rw [firstHead.unique secondHead, firstTail.unique secondTail]
end

theorem TaskForest.cost_unique {expand : Task → Expansion Task Answer Obligation} {tasks : List Task}
    (first second : TaskForest expand tasks) : first.cost = second.cost :=
  congrArg TaskForest.cost (first.unique second)

theorem TaskForest.answers_unique {expand : Task → Expansion Task Answer Obligation} {tasks : List Task}
    (first second : TaskForest expand tasks) : first.answers = second.answers :=
  congrArg TaskForest.answers (first.unique second)

theorem TaskForest.cursorDebt_unique {expand : Task → Expansion Task Answer Obligation}
    (state : State Task Answer Obligation) (first second : TaskForest expand state.agenda)
    (cursor scale : Nat) : first.cursorDebt state cursor scale = second.cursorDebt state cursor scale :=
  congrArg (fun forest => forest.cursorDebt state cursor scale) (first.unique second)

end Mettapedia.OSLF.MeTTaIL.GeneralPremise.Scheduler
