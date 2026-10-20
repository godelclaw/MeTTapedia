import Mettapedia.OSLF.MeTTaIL.ScopedCollectionReplay
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachineControls

/-! Receipt checking rejects fabricated evidence even for attainable results. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine.ReplayControls

open Syntax CollectionSelection ScopedRuleMatching
open ScopedCollectionMatching.Controls (a b)
open ScopedCollectionMachine.Controls (setRequest bagRequest)

def sample : Receipt :=
  { allocation := ⟨[a, a], [], [⟨0, true⟩, ⟨0, false⟩]⟩
    matching := ⟨[("R", ⟨[], 0, .collection .hashSet [] none⟩),
      ("Y", ⟨[], 0, a⟩), ("X", ⟨[], 0, a⟩)], []⟩ }

def controls : List (String × Bool) :=
  let published := publication (resume setRequest 30 (start setRequest))
  [ ("all-published-set-receipts-check", published.all (checkReceipt setRequest))
  , ("all-published-bag-origins-check",
      (publication (resume bagRequest 30 (start bagRequest))).all (checkReceipt bagRequest))
  , ("independently-written-receipt-checks", checkReceipt setRequest sample)
  , ("out-of-range-origin-refused", !checkReceipt setRequest
      { sample with allocation := { sample.allocation with decisions := [⟨9, true⟩, ⟨0, false⟩] } })
  , ("missing-allocation-decision-refused", !checkReceipt setRequest
      { sample with allocation := { sample.allocation with decisions := [⟨0, true⟩] } })
  , ("illegal-bag-retention-refused", !checkReceipt bagRequest sample)
  , ("changed-selected-value-refused", !checkReceipt setRequest
      { sample with allocation := { sample.allocation with values := [b, a] } })
  , ("changed-residual-refused", !checkReceipt setRequest
      { sample with allocation := { sample.allocation with residual := [a] } })
  , ("changed-capture-refused", !checkReceipt setRequest
      { sample with matching := { sample.matching with assignment := [("X", ⟨[], 0, b⟩)] } })
  , ("extra-nested-history-refused", !checkReceipt setRequest
      { sample with matching := { sample.matching with trace := [⟨[0], 0⟩] } })
  , ("wrong-authored-path-refused", !checkReceipt { setRequest with path := [9] } sample)
  , ("wrong-ambient-context-refused", !checkReceipt { setRequest with ambient := 1 } sample) ]

def checkControls : IO Unit := do
  for (name, passed) in controls do
    if !passed then throw (IO.userError s!"Collection replay control failed: {name}")
  IO.println s!"ScopedCollectionReplayControls: {controls.length}/{controls.length}"

#eval checkControls

end Mettapedia.OSLF.MeTTaIL.ScopedCollectionMachine.ReplayControls
