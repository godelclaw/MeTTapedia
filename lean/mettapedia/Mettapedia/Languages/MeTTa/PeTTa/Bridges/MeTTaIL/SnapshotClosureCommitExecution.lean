import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureFiringExecution

/-! Checked commits preserve both fact membership and logical key identity.
The extra unpublished-key list is internal to the native commit operation;
the model projection retains the complete fact and key lists. -/

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

deriving instance ReflBEq, LawfulBEq for ClosureMachine.Key

private theorem binding_term_injective : Function.Injective
    (fun entry : String × Pattern => Term.application "Binding" [.string entry.1,InferenceCettaWire.encodePattern entry.2]) := by
  rintro ⟨leftName,left⟩ ⟨rightName,right⟩ same
  have arguments := (Term.application.inj same).2
  have names := Term.string.inj (List.cons.inj arguments).1
  have values := InferenceCettaWire.encodePattern_injective (List.cons.inj (List.cons.inj arguments).2).1
  cases names
  cases values
  rfl

theorem keyTerm_injective : Function.Injective ClosureMachine.keyTerm := by
  rintro ⟨leftIndex,leftValues,leftPremises⟩ ⟨rightIndex,rightValues,rightPremises⟩ same
  have arguments := (Term.application.inj same).2
  have indices := Term.natural.inj (List.cons.inj arguments).1
  have values := encodeList_injective _ binding_term_injective (List.cons.inj (List.cons.inj arguments).2).1
  have premises := encodeList_injective _ InferenceCettaWire.encodePattern_injective
    (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).1
  cases indices
  cases values
  cases premises
  rfl

theorem member_returns {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (element : α → Term) (injective : Function.Injective element) (state : State) (item : α) (items : List α) :
    PureReturns runtime [] state
      (apply "gslt:automata:member" [encoded (element item),encoded (encodeList element items)]) state
      (Effects.boolean (items.contains item)) := by
  have common := CompleteExecution.complete_member_returns element injective state item items
  have runner := runner_from_base% ["item","items"] common using RetainedMatchingWire.scopedPrimitive_agreement
  have actual := Library.lift_call (L := library) checked (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["item","items"] (by decide) rfl (by decide +kernel) runner
  by_cases present : item ∈ items <;> simpa [runtime,WireKit.apply,List.contains_eq_mem,present] using actual

private def commitTerm (added : List ClosureMachine.Key) :
    Option (List Pattern × List ClosureMachine.Key) → Term :=
  encodeOption fun result => .application "SnapshotCommit"
    [factsTerm result.1,encodeList ClosureMachine.keyTerm result.2,encodeList ClosureMachine.keyTerm added]

theorem commit_returns (state : State) (prepared : Executable.Prepared) (snapshot : List Pattern)
    (batch : List GeneralOccurrenceSemantics.Receipt) (facts : List Pattern) (keys added : List ClosureMachine.Key) :
    ∃ published, PureReturns runtime [] state
      (apply "gslt:snapshot:commit"
        [encoded (ClosureMachine.metadataTerm prepared),encoded (factsTerm snapshot),
         encoded (encodeList CompleteExecution.classReceiptTerm batch),encoded (factsTerm facts),
         encoded (encodeList ClosureMachine.keyTerm keys),encoded (encodeList ClosureMachine.keyTerm added)]) state
      (encoded (commitTerm published (ClosureMachine.commit? prepared snapshot batch facts keys))) := by
  induction batch generalizing facts keys added with
  | nil =>
    refine ⟨added,?_⟩
    metta_call checked
    metta_eval with checked unfolding [ClosureMachine.commit?,commitTerm,factsTerm]
  | cons receipt rest ih =>
    have firing := firing_returns state prepared snapshot receipt
    cases found : ClosureMachine.key? prepared snapshot receipt with
    | none =>
      rw [found] at firing
      refine ⟨[],?_⟩
      simp only [ClosureMachine.commit?,found]
      metta_call checked
      metta_eval [firing] with checked unfolding [commitTerm,factsTerm]
    | some key =>
      rw [found] at firing
      have front : ClosureMachine.commit? prepared snapshot (receipt :: rest) facts keys =
          ClosureMachine.commit? prepared snapshot rest (ClosureMachine.insert facts receipt.target)
            (ClosureMachine.insert keys key) := by
        simp only [ClosureMachine.commit?,found]
        rfl
      obtain ⟨published,continued⟩ := ih (ClosureMachine.insert facts receipt.target)
        (ClosureMachine.insert keys key) (if keys.contains key then added else added ++ [key])
      refine ⟨published,?_⟩
      have factMember := member_returns InferenceCettaWire.encodePattern
        InferenceCettaWire.encodePattern_injective state receipt.target facts
      have keyMember := member_returns ClosureMachine.keyTerm keyTerm_injective state key keys
      have factAppend := append_returns InferenceCettaWire.encodePattern state facts [receipt.target]
      have keyAppend := append_returns ClosureMachine.keyTerm state keys [key]
      have addedAppend := append_returns ClosureMachine.keyTerm state added [key]
      cases factSeen : facts.contains receipt.target <;> cases keySeen : keys.contains key <;>
        (rw [factSeen] at factMember
         rw [keySeen] at keyMember
         simp only [ClosureMachine.insert,factSeen,keySeen,Bool.false_eq_true,if_false,if_true] at continued
         rw [front]
         simp only [ClosureMachine.insert,factSeen,keySeen,Bool.false_eq_true,if_false,if_true]
         metta_call checked
         metta_eval [firing,factMember,keyMember,factAppend,keyAppend,addedAppend,continued] with checked unfolding
           [ClosureMachine.insert,factSeen,keySeen,commitTerm,factsTerm])

#print axioms keyTerm_injective
#print axioms member_returns
#print axioms commit_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
