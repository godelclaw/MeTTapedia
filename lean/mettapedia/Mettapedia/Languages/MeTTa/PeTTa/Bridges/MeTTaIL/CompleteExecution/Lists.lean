import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.BridgeCoverage

/-!
# List helpers of the complete machine
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Effects (State)
open Eval
open BridgeKit WireKit

abbrev terms (values : List Term) : Atom := encoded (encodeList id values)

/-- `gslt:complete:drop` is `List.drop`. -/
@[metta_head "gslt:complete:drop"]
theorem drop_returns (state : State) : ∀ (count : Nat) (items : List Term),
    PureReturns runtime [] state (apply "gslt:complete:drop" [number count, terms items]) state
      (terms (items.drop count)) := by
  intro count
  induction count with
  | zero => intro items; metta_call_in completeProof_checked using completeProof_agreement; metta_eval with completeProof_checked in completeProof_agreement
  | succ count ih =>
    intro items
    metta_call_in completeProof_checked using completeProof_agreement
    cases items <;> metta_eval [ih _] with completeProof_checked in completeProof_agreement

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.drop_returns
