import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentationProofs
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionControls

/-! # Complete ordinary replay and altered-history controls -/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentation.Controls

open Syntax RuleBinding ScopedRuleMatching CollectionSelection
open EquationalScopedMatching.Controls
open ScopedCollectionMatching.Controls (a b spec)

structure Case where
  label : String
  path : List Nat
  schema : Pattern
  target : Pattern
  events : List EquationalScopedReceipts.Event
  expected : Option (Pattern × List EquationalScopedReceipts.Event)

def setEvent (decisions : List Decision) : EquationalScopedReceipts.Event :=
  ⟨[], .hashSet, decisions⟩

def cases : List Case :=
  [⟨"set-duplicate-presentation", [], set [x,y], set [a],
      [setEvent [⟨0,true⟩,⟨0,false⟩]], some (set [a,a], [])⟩,
   ⟨"set-retained-residual", [], set [x,y] (some "R"), set [a],
      [setEvent [⟨0,true⟩,⟨0,true⟩]], some (set [a,a,a], [])⟩,
   ⟨"bag-second-occurrence", [], bag [x] (some "R"), bag [a,a],
      [⟨[],.hashBag,[⟨1,false⟩]⟩], some (bag [a,a], [])⟩,
   ⟨"wrong-event-path", [], set [x], set [a],
      [⟨[1],.hashSet,[⟨0,false⟩]⟩], none⟩,
   ⟨"wrong-event-kind", [], set [x], set [a],
      [⟨[],.hashBag,[⟨0,false⟩]⟩], none⟩,
   ⟨"wrong-decision-count", [], set [x,y], set [a],
      [setEvent [⟨0,false⟩]], none⟩,
   ⟨"bag-cannot-retain", [], bag [x], bag [a],
      [⟨[],.hashBag,[⟨0,true⟩]⟩], none⟩,
   ⟨"out-of-range", [], set [x], set [a],
      [setEvent [⟨1,false⟩]], none⟩,
   ⟨"missing-event", [], set [x], set [a], [], none⟩,
   ⟨"unused-event-retained", [], x, a, [setEvent []], some (a,[setEvent []])⟩,
   ⟨"open-target-refused", [], set [x], set [a] (some "R"),
      [setEvent [⟨0,false⟩]], none⟩,
   ⟨"wrong-constructor-refused", [], .apply "First" [x], .apply "Second" [a], [], none⟩]

def checkControls : IO Unit := do
  for test in cases do
    unless presentAt test.path test.schema test.target test.events == test.expected do
      throw (IO.userError s!"Presentation control failed: {test.label}")
  for test in RecursiveCollectionMachine.Controls.cases do
    for answer in (RecursiveCollectionMachine.Controls.finished test).answers do
      let request := test.request
      let some (presented, []) := presentAt request.path request.schema request.target answer.trace
        | throw (IO.userError s!"Presentation replay failed: {test.label}")
      unless GeneralScopedMatchReplay.replayAt request.rule request.spec request.ambient request.site
          request.path request.depth request.initial request.schema presented
          (frontTraceAt request.path request.schema) == some (answer.assignment, []) do
        throw (IO.userError s!"Ordinary replay differs: {test.label}")
  IO.println s!"RecursiveCollectionPresentationControls: {cases.length} altered-history controls and all published receipts"

#eval checkControls

/- Distinct physical bag selections may use the same ordinary witness. The
allocation histories remain different, so witness equality cannot identify
their declared occurrences. -/
#guard presentAt [] (bag [x] (some "R")) (bag [a,a]) [⟨[],.hashBag,[⟨0,false⟩]⟩] =
  presentAt [] (bag [x] (some "R")) (bag [a,a]) [⟨[],.hashBag,[⟨1,false⟩]⟩]

#guard (⟨[],.hashBag,[⟨0,false⟩]⟩ : EquationalScopedReceipts.Event) ≠ ⟨[],.hashBag,[⟨1,false⟩]⟩

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionPresentation.Controls
