import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionReplay

/-! Exact decoding and independent validation of returned collection receipts. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching
  CollectionSelection ScopedCollectionMachine
open CollectionSelectionExecution ScopedCollectionExecution
open RuleInstantiationExecution.GeneralExecution

private def assignmentEntry? : Term → Option (String × ContextualValue)
  | .application "Binding" [.string name, value] => do
      pure (name, ← InferenceCettaWire.AuthoredRule.decodeContextualValue? value)
  | _ => none

def assignment? (wire : Term) : Option Assignment := decodeList assignmentEntry? wire

@[simp] theorem assignment?_term (assignment : Assignment) :
    assignment? (RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment) =
      some assignment := by
  have encoded : RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm assignment =
      encodeList (fun entry => .application "Binding"
        [.string entry.1, InferenceCettaWire.AuthoredRule.contextualValueTerm entry.2]) assignment := by
    simp only [RuleInstantiationExecution.ScopedCapture.scopedAssignmentTerm,
      MatchAutomataBindingExecution.payloadBindingsTerm, encodeList_map,
      Function.comp_def, MatchAutomataBindingExecution.payloadBindingTerm]
  rw [assignment?, encoded]
  apply decodeList_encodeList
  intro entry
  simp [assignmentEntry?]

private def natural? : Term → Option Nat
  | .natural value => some value
  | _ => none

private def bagChoice? : Term → Option GeneralScopedMatchMachine.BagChoice
  | .application "BagChoice" [path, .natural selected] => do
      pure ⟨← decodeList natural? path, selected⟩
  | _ => none

private theorem bagChoice?_term (choice : GeneralScopedMatchMachine.BagChoice) :
    bagChoice? (bagChoiceTerm choice) = some choice := by
  have paths : decodeList natural? (encodeList Term.natural choice.path) = some choice.path :=
    decodeList_encodeList natural? Term.natural (fun _ => rfl) choice.path
  cases choice
  simp [bagChoice?, bagChoiceTerm, paths]

def trace? (wire : Term) : Option (List GeneralScopedMatchMachine.BagChoice) :=
  decodeList bagChoice? wire

@[simp] theorem trace?_term (trace : List GeneralScopedMatchMachine.BagChoice) :
    trace? (traceTerm trace) = some trace :=
  decodeList_encodeList _ _ bagChoice?_term trace

def flag? : Term → Option Bool
  | .natural 0 => some false
  | .natural 1 => some true
  | _ => none

@[simp] theorem flag?_booleanTerm (value : Bool) : flag? (booleanTerm value) = some value := by
  cases value <;> rfl

def decision? : Term → Option Decision
  | .application "CollectionDecision" [.natural index, retained] =>
      (fun kept => ⟨index, kept⟩) <$> flag? retained
  | _ => none

@[simp] theorem decision?_decisionTerm (decision : Decision) :
    decision? (decisionTerm decision) = some decision := by
  cases decision
  simp [decision?, decisionTerm]

def allocation? : Term → Option (Allocation Pattern)
  | .application "CollectionAllocation" [values, residual, decisions] => do
      pure ⟨← CettaWire.decodeList InferenceCettaWire.decodePattern values,
        ← CettaWire.decodeList InferenceCettaWire.decodePattern residual,
        ← CettaWire.decodeList decision? decisions⟩
  | _ => none

@[simp] theorem allocation?_allocationTerm (allocation : Allocation Pattern) :
    allocation? (allocationTerm InferenceCettaWire.encodePattern allocation) = some allocation := by
  cases allocation
  simp [allocation?, allocationTerm]

def answer? : Term → Option GeneralScopedMatchMachine.Answer
  | .application "ScopedMatcherAnswer" [assignment, trace] => do
      pure ⟨← assignment? assignment, ← trace? trace⟩
  | _ => none

@[simp] theorem answer?_matcherAnswerTerm (answer : GeneralScopedMatchMachine.Answer) :
    answer? (matcherAnswerTerm answer) = some answer := by
  cases answer
  simp [answer?, matcherAnswerTerm]

def receipt? : Term → Option Receipt
  | .application "CollectionReceipt" [allocation, answer] => do
      pure ⟨← allocation? allocation, ← answer? answer⟩
  | _ => none

@[simp] theorem receipt?_receiptTerm (receipt : Receipt) :
    receipt? (receiptTerm receipt) = some receipt := by
  cases receipt
  simp [receipt?, receiptTerm]

theorem receiptTerm_injective : Function.Injective receiptTerm := by
  intro first second same
  have decoded := congrArg receipt? same
  simpa only [receipt?_receiptTerm, Option.some.injEq] using decoded

def check (request : Request) (wire : Term) : Bool :=
  match receipt? wire with
  | none => false
  | some receipt => checkReceipt request receipt

theorem check_exact (request : Request) (wire : Term) :
    check request wire = true ↔ ∃ receipt, receipt? wire = some receipt ∧ Valid request receipt := by
  cases decoded : receipt? wire with
  | none => simp [check, decoded]
  | some receipt => simp [check, decoded, checkReceipt_exact]

theorem check_encoded_exact (request : Request) (receipt : Receipt) :
    check request (receiptTerm receipt) = true ↔ Valid request receipt := by
  simp [check, checkReceipt_exact]

def firing? : Term → Option FiringReceipt
  | .application "CollectionFiring" [receipt, target] => do
      pure ⟨← receipt? receipt, ← InferenceCettaWire.decodePattern target⟩
  | _ => none

@[simp] theorem firing?_firingTerm (firing : FiringReceipt) :
    firing? (firingTerm firing) = some firing := by
  cases firing
  simp [firing?, firingTerm]

def checkFiring (request : Request) (wire : Term) : Bool :=
  match firing? wire with
  | none => false
  | some firing =>
      checkReceipt request firing.source &&
        decide (ScopedRuleMatching.reduct? request.rule request.spec request.ambient
          firing.source.matching.assignment = some firing.target)

theorem checkFiring_exact (request : Request) (wire : Term) :
    checkFiring request wire = true ↔ ∃ firing,
      firing? wire = some firing ∧ Valid request firing.source ∧
        ScopedRuleMatching.reduct? request.rule request.spec request.ambient
          firing.source.matching.assignment = some firing.target := by
  cases decoded : firing? wire with
  | none => simp [checkFiring, decoded]
  | some firing => simp [checkFiring, decoded, checkReceipt_exact]

example : flag? (.natural 2) = none := rfl
example : flag? (.symbol "True") = none := rfl
example : receipt? (.application "CollectionReceipt" []) = none := rfl
example : firing? (.application "CollectionFiring" []) = none := rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionCodec
