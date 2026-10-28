import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureSearchExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceSearchExecution

/-! Initialization deduplicates the declared fact-set observation, installs
its checked provider and initializes the same retained shared search state. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit

private instance : LawfulBEq Pattern where
  rfl := by intro value; change decide (value = value) = true; simp
  eq_of_beq := by intro left right same; change decide (left = right) = true at same; exact of_decide_eq_true same

private theorem erased_patterns_map (patterns seen : List Pattern) :
    List.eraseDupsBy.loop (· == ·) (patterns.map InferenceCettaWire.encodePattern)
      (seen.map InferenceCettaWire.encodePattern) =
    (List.eraseDupsBy.loop (· == ·) patterns seen).map InferenceCettaWire.encodePattern := by
  induction patterns generalizing seen with
  | nil => simp [List.eraseDupsBy.loop]
  | cons first rest ih =>
    have contains : (seen.map InferenceCettaWire.encodePattern).contains (InferenceCettaWire.encodePattern first) =
        seen.contains first := by
      apply Bool.eq_iff_iff.mpr
      simp [InferenceCettaWire.encodePattern_injective.eq_iff]
    simp only [List.map_cons,List.eraseDupsBy.loop,List.any_beq,contains]
    cases present : seen.contains first
    · simpa [present,List.map_cons] using ih (first :: seen)
    · simpa [present] using ih seen

theorem unique_patterns_returns (state : State) (patterns : List Pattern) :
    PureReturns runtime [] state (apply "gslt:automata:unique" [encoded (factsTerm patterns)]) state
      (encoded (factsTerm patterns.eraseDups)) := by
  have original := CollectionOccurrenceSearchExecution.Declared.unique_returns CompleteEmission.runtime
    CollectionOccurrenceSearchExecution.Declared.key_metadata_agreement state (patterns.map InferenceCettaWire.encodePattern)
  have actual := Library.lift_call (L := library) checked (by decide +kernel) (by decide)
    (by decide +kernel) (by decide) ["patterns"] (by decide) rfl (by decide +kernel) original
  have mapped : (patterns.map InferenceCettaWire.encodePattern).eraseDups =
      patterns.eraseDups.map InferenceCettaWire.encodePattern := erased_patterns_map patterns []
  simpa [SnapshotClosureExecution.runtime,WireKit.apply,factsTerm,encodeList_map,mapped] using actual

private theorem closed_of_admitted (prepared : Executable.Prepared) (facts : List Pattern)
    (admitted : (Executable.plan prepared facts).complete = true) : ClosureMachine.closed prepared facts = true :=
  (GeneralExecutionAdmission.complete_snapshot_checks admitted).2.2.1

theorem begin_returns (state : State) (prepared : Executable.Prepared)
    (admitted : (Executable.plan prepared prepared.seedFacts.eraseDups).complete = true) :
    PureReturns runtime [] state
      (apply "gslt:snapshot:begin"
        [encoded (CompletePlanWire.planTerm (Executable.plan prepared prepared.seedFacts)
          (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
         encoded (ClosureMachine.standardTerm prepared),
         encoded (InferenceCettaWire.encodePattern (Executable.request prepared.vocabulary)),
         encoded (ClosureMachine.metadataTerm prepared),encoded (.string Query.factRelation),
         encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows),
         encoded (factsTerm prepared.seedFacts)]) state
      (encoded (ClosureMachine.machineTerm prepared (ClosureMachine.begin prepared))) := by
  have closed := closed_of_admitted prepared prepared.seedFacts.eraseDups admitted
  have unique := unique_patterns_returns state prepared.seedFacts
  have plan := plan_returns state prepared prepared.seedFacts prepared.seedFacts.eraseDups
  rw [closed] at plan
  change PureReturns runtime [] state
    (apply "gslt:snapshot:plan"
      [encoded (CompletePlanWire.planTerm (Executable.plan prepared prepared.seedFacts)
        (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement")),
       encoded (.string Query.factRelation),encoded (factsTerm prepared.seedFacts.eraseDups),
       encoded (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows)]) state
    (encoded (encodeOption id (some (CompletePlanWire.planTerm (Executable.plan prepared prepared.seedFacts.eraseDups)
      (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement"))))) at plan
  have search := search_zero_returns state prepared prepared.seedFacts.eraseDups prepared.seedFacts.eraseDups admitted closed
  simp only [ClosureMachine.begin,ClosureMachine.machineTerm,closed,if_true]
  metta_call checked
  metta_eval [unique,plan,search] with checked unfolding [ClosureMachine.begin,ClosureMachine.machineTerm,closed,
    ClosureMachine.spec,factsTerm,CompleteExecution.classSearchBackend]

#print axioms unique_patterns_returns
#print axioms begin_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
