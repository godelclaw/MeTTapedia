import Mettapedia.GSLT.LanguageDef.CollectionNestedConsumerControls
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch

/-!
# Chronological publication controls for nested guarded allocations

The delayed-allocation control compares full origin packets. Counting targets
alone would miss the duplicate produced by draining a flattened publication.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CollectionNestedBatchControls

open Mettapedia.OSLF.MeTTaIL _root_.Mettapedia.OSLF.MeTTaIL.Syntax CollectionOccurrenceBatch
open CollectionOccurrenceHandoff

def allocations (permitted : Bool) (source : Pattern) (bound : List TypeExpr := []) :
    List (Allocation (CollectionNestedConsumerControls.plan permitted) bound (.base "Workspace") source) :=
  (jobs (CollectionNestedConsumerControls.plan permitted) bound (.base "Workspace") source).attach.flatMap
    fun selected =>
      let job := selected.val
      let licensed := (jobs_exact _ _ _ _ _).mp selected.property
      let matched := RecursiveCollectionMachine.run job.request 100
        (RecursiveCollectionMachine.start job.request)
      matched.answers.attach.filterMap fun answer =>
        allocate? job licensed 100 answer.val answer.property 0

def source := CollectionNestedConsumerControls.source

def initial (permitted : Bool) := State.begin (allocations permitted source)

def finished (permitted : Bool) := State.run 80 (initial permitted)

def readout (packet : Publication) :=
  (packet.job.origin.ordinal, packet.job.variant.site.address, packet.answer.trace, packet.outcome)

/-- A later allocation has published while an earlier one is one tick short
of publication. The seeded log already accounts for the later result. -/
def skewed : State (CollectionNestedConsumerControls.plan true) [] (.base "Workspace") source :=
  match (allocations true source).map Frame.initial with
  | first :: second :: _ =>
    let pause := ((List.range 80).find? fun work =>
      (Frame.run work first).publication.isEmpty &&
        !(Frame.run (work + 1) first).publication.isEmpty).getD 0
    let frames := [Frame.run pause first, Frame.run 80 second]
    ⟨frames, frames.flatMap Frame.publication⟩
  | frames => ⟨frames, frames.flatMap Frame.publication⟩

theorem skewed_balanced : skewed.Balanced := by
  unfold State.Balanced
  unfold skewed
  split <;> exact List.Perm.refl _

/-- The rejected algorithm loses the earlier occurrence and repeats the
later one, even though its final answer-value count still looks correct. -/
def flattenedCursorRound {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} (batch : State plan bound expected source) :
    State plan bound expected source :=
  let frames := batch.frames.map (Frame.run 1)
  ⟨frames, batch.log ++ (frames.flatMap Frame.publication).drop
    (batch.frames.flatMap Frame.publication).length⟩

def checkControls : IO Unit := do
  for permitted in [true, false] do
    let batch := initial permitted
    unless batch.frames.length == 2 && batch.log.isEmpty do
      throw (IO.userError "Nested batch lost an allocation or published before its guard")
    let done := finished permitted
    unless done.log.length == (if permitted then 2 else 0) do
      throw (IO.userError "Nested batch guard produced the wrong receipt count")
    unless done.log.all (fun packet =>
        (packet.finish? (CollectionNestedConsumerControls.plan permitted) [] (.base "Workspace")).isSome) do
      throw (IO.userError "Nested batch produced an unfinished outer receipt")
    let resumed := State.run 47 (State.run 33 batch)
    unless resumed.log.map readout == done.log.map readout do
      throw (IO.userError "Nested batch resumption changed the receipt account")
  let before := skewed
  let after := before.round
  let rejected := flattenedCursorRound before
  unless before.log.length == 1 && after.log.length == 2 && rejected.log.length == 2 do
    throw (IO.userError "Delayed-allocation control has the wrong shape")
  unless after.log.map readout != rejected.log.map readout do
    throw (IO.userError "Flattened cursor regression failed to distinguish source origins")
  unless (after.log.map (fun packet => packet.answer.trace)).eraseDups.length == 2 &&
      (rejected.log.map (fun packet => packet.answer.trace)).eraseDups.length == 1 do
    throw (IO.userError "Chronological publication lost or repeated an allocation origin")
  IO.println "NestedCollectionBatchControls: exact chronological origins and rejected flattened cursor passed"

#eval checkControls

end Mettapedia.GSLT.LanguageDef.CollectionNestedBatchControls
