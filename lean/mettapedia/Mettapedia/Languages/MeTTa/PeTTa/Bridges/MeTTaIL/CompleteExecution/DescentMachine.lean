import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.DescentReadout
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Scoped

/-!
# The descent machine's environment and commit

The environment value every descent head receives, and `gslt:premise:machine-commit` in the
descent machine's runtime: the step that `gslt:descent:tick` takes after expanding a task.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open StructuralDescent.Scheduled (Goal Result Task Obligation)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec
open PremiseSchedulerExecution (schedulerStateTerm schedulerExpansionTerm)

/-- `gslt:premise:machine-commit`, in the descent machine's runtime. -/
theorem descent_commit_returns {Task Answer Obligation : Type} (state : State)
    (task : Task → Term) (answer : Answer → Term) (obligation : Obligation → Term)
    (expand : Task → Scheduler.Expansion Task Answer Obligation)
    (scheduler : Scheduler.State Task Answer Obligation) :
    PureReturns descentLibrary.runtime [] state
      (apply "gslt:premise:machine-commit" [encoded (schedulerStateTerm task answer obligation scheduler),
        encoded (encodeOption (schedulerExpansionTerm task answer obligation) (scheduler.agenda.head?.map expand))])
      state (encoded (encodeOption (schedulerStateTerm task answer obligation) (some (Scheduler.tick expand scheduler)))) := by
  metta_lift descent_checked ["state", "expanded"]
    (by metta_lift typed_checked ["state", "expanded"] (machine_commit_returns state task answer obligation expand scheduler))

abbrev environmentValue (environment : Environment) (free : List (String × TypeExpr)) : Atom :=
  encoded (PremiseOperationsExecution.GeneralExecution.environmentTerm environment free)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
