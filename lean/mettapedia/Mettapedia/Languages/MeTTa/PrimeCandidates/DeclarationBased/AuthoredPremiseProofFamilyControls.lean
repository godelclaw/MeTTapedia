import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseProofFamily
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseControls

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

/-! Positive and negative controls for the native receipt proof-program image,
original conditional and recursive receipts, raw rest captures, and discovery. -/

set_option autoImplicit false
open Mettapedia.OSLF.MeTTaIL
open Syntax RuleBinding ScopedRuleMatching
open GeneralPremise GeneralExecutionAdmission
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open AuthoredPremiseProofFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseProofFamily.Controls

private def type : TypeExpr := .base "Nat"
private def zero : Pattern := .apply "Zero" []
private def successor (value : Pattern) : Pattern := .apply "Successor" [value]
private def numeral : Nat → Pattern | 0 => zero | n + 1 => successor (numeral n)

/-- The declaration depends on itself, and its base case has a larger index.
Every finite receipt records the actual smaller source child. -/
private def recursiveRule : RewriteRule where
  name := "recursive-check"
  typeContext := [("X", type)]
  left := successor (.fvar "X")
  right := zero
  premises := [.congruence (.fvar "X") zero]

private def baseRule : RewriteRule where
  name := "base-check"
  typeContext := []
  left := zero
  right := zero
  premises := []

private def language : LanguageDef where
  name := "finite-recursive-receipts"
  types := ["Nat"]
  terms := [
    {label := "Zero", category := "Nat", params := [], syntaxPattern := []},
    {label := "Successor", category := "Nat", params := [.simple "value" type], syntaxPattern := []}]
  equations := []
  rewrites := [recursiveRule, baseRule]

private def environment : Environment where
  language := language
  free := fun _ => none
  provider := ⟨[], [], []⟩
  specifications := [(0, GeneralRuleBindingInference.inferredSpec recursiveRule),
    (1, GeneralRuleBindingInference.inferredSpec baseRule)]

private def captured (n : Nat) : Assignment := [("X", localValue [] (numeral n))]

private def history : Nat → List Event
  | 0 => [.child 0 0 1 [] zero zero [] [] [] [] []]
  | n + 1 => [.child 0 0 0 [] (numeral (n + 1)) zero [] [] (captured n) (captured n) (history n)]

private def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
private def plan : Plan := compile snapshot {sites := .rootOnly, includeDerivedEquations := false}
private def candidate (job : GeneralRuleJobs.Job) : GeneralRuleJobs.Receipt :=
  ⟨job, [], captured 1, captured 1, history 1, zero, zero⟩
private def jobs := GeneralRuleJobs.jobs plan [] type (numeral 2)

private def scope : Lean.Name := `receiptFamilyScope
private def handler : Lean.Name := `receiptFamilyHandler
private def claim : Claim := (numeral 2, zero)
private def dynamic : DynamicProvider := .empty
private def actual? : Option Proof :=
  (jobs.map candidate).find? (GeneralPremiseNativeEvidence.check dynamic plan [] type claim)

def checksFor (actual : Proof) : List (String × Bool) :=
  let invalid : Proof := {actual with premiseHistory := []}
  let nativeRequest : Tower.Tm 0 := requestAt scope handler plan [] type claim
  let nativeReceipt : Tower.Tm 0 := receiptAt scope handler plan [] type actual
  let nativeProgram : Tower.Tm 0 := program scope handler plan [] type claim actual
  let nativeInvalid : Tower.Tm 0 := program scope handler plan [] type claim invalid
  let wrongRole : Tower.Tm 0 := packProgram nativeRequest nativeRequest
  let wrongWitness : Tower.Tm 0 := .app (.app FormationSensitive.DependentComputation.ReceiptPacking.pack nativeReceipt)
    (.refl (requestAt scope handler plan [] type (zero, zero)))
  let wrongProgram : Tower.Tm 0 := .app (.app (.lam (.var 0)) nativeReceipt) (.refl nativeRequest)
  let decoder := nativeRootDecoder scope handler dynamic plan [] type
  let rootAccepted : Bool := StructuralConversionCode.Code.check codeHeadPolicy decoder.decode
    (rootCode claim actual) (checking nativeRequest nativeReceipt) nativeRequest
  let equalityAccepted : Bool := StructuralConversionCode.Code.check codeHeadPolicy decoder.decode
    (equalityCode scope handler plan [] type claim actual)
    (.id NativeWireData.dataType nativeRequest nativeRequest)
    (FormationSensitive.DependentComputation.ReceiptPacking.equalityType NativeWireData.dataName
      (.const checkerName) nativeRequest nativeReceipt)
  let compiled := compileProgram? scope handler dynamic plan [] type .nil claim actual
  let evaluated := (evaluationCode scope handler plan [] type claim actual).check codeHeadPolicy
    FormationCheckedTelescopePrograms.noRoot nativeProgram (.pair nativeReceipt (.refl nativeRequest))
  let discoveryOutput := (Discovery.operation scope handler dynamic plan [] type .nil).run ((zero, zero), 128)
  let baseRequest : Tower.Tm 0 := requestAt scope handler plan [] type (zero, zero)
  [
  ("native-program-beta-certificate", evaluated),
  ("native-program-selected-beta-count", (evaluationCode (n := 0) scope handler plan [] type claim actual).stepCount == 2),
  ("actual-discovery-operation-produces-native-programs", !discoveryOutput.2.isEmpty),
  ("actual-discovery-journal-native-program-coverage", discoveryOutput.2.length ==
    (GeneralPremiseNativeDiscovery.discovered discoveryOutput.1).length),
  ("every-discovered-native-program-checks", discoveryOutput.2.all (checkProgram scope handler dynamic plan [] type baseRequest)),
  ("actual-discovery-cursor-retained", discoveryOutput.1.2.2.cursor == 128),
  ("source-total-recursive-receipt", GeneralPremiseNativeEvidence.check dynamic plan [] type claim actual),
  ("ordinary-source-stratification-gate-remains-false", !plan.complete),
  ("actual-source-declaration-ordinal", actual.job.ordinal == 0),
  ("recursive-and-later-declaration-children-retained", GeneralPremiseReceiptWire.eventsCodec.put actual.premiseHistory == GeneralPremiseReceiptWire.eventsCodec.put (history 1)),
  ("selected-native-root-certificate", rootAccepted),
  ("selected-dependent-equality-certificate", equalityAccepted),
  ("compiler-returns-actual-judgment", compiled.isSome),
  ("typed-compiler-literal-program", compiled.map Subtype.val == some nativeProgram),
  ("wrong-source-bound-header-refuses", !(checkProgram scope handler dynamic plan [type] type
    (requestAt (n := 1) scope handler plan [] type claim)
    (program (n := 1) scope handler plan [] type claim actual))),
  ("actual-native-proof-program-image", checkProgram scope handler dynamic plan [] type nativeRequest nativeProgram),
  ("original-receipt-readback", (readProgram? scope handler dynamic plan [] type nativeRequest nativeProgram).map
    GeneralPremiseReceiptWire.encodeReceipt == some (GeneralPremiseReceiptWire.encodeReceipt actual)),
  ("actual-native-service-invocation", (SemanticServiceInvocation.invoke
    (invocation scope handler dynamic plan [] type nativeRequest nativeProgram)).acceptedValue.isSome),
  ("well-formed-data-invalid-source-receipt", !GeneralPremiseNativeEvidence.check dynamic plan [] type claim invalid),
  ("well-formed-forged-program-refuses", !(checkProgram scope handler dynamic plan [] type nativeRequest nativeInvalid)),
  ("forged-root-has-no-decoded-endpoints", (decoder.decode (n := 0) (claim, invalid)).isNone),
  ("wrong-request-target-refuses", !(checkProgram scope handler dynamic plan [] type
    (requestAt scope handler plan [] type (numeral 2, numeral 1)) nativeProgram)),
  ("wrong-receipt-role-refuses", !(checkProgram scope handler dynamic plan [] type nativeRequest wrongRole)),
  ("wrong-scope-refuses", !(checkProgram `wrongScope handler dynamic plan [] type nativeRequest nativeProgram)),
  ("wrong-handler-refuses", !(checkProgram scope `wrongHandler dynamic plan [] type nativeRequest nativeProgram)),
  ("changed-source-type-refuses", !(checkProgram scope handler dynamic plan [] (.base "Other") nativeRequest nativeProgram)),
  ("changed-source-plan-refuses", !(checkProgram scope handler dynamic {plan with rules := []} [] type nativeRequest nativeProgram)),
  ("wrong-equality-witness-request-refuses", !(checkProgram scope handler dynamic plan [] type nativeRequest wrongWitness)),
  ("wrong-native-function-refuses", !(checkProgram scope handler dynamic plan [] type nativeRequest wrongProgram)),
  ("raw-data-is-not-a-native-proof-program", !(checkProgram scope handler dynamic plan [] type nativeRequest nativeReceipt)),
  ("terminal-pair-not-assumed-selected-program", !(checkProgram scope handler dynamic plan [] type nativeRequest
    (.pair nativeReceipt (.refl nativeRequest)))),
  ("malformed-native-lambda-refuses", !(checkProgram scope handler dynamic plan [] type nativeRequest (.lam (.var 0)))),
  ("malformed-receipt-packet-refuses", !(checkProgram scope handler dynamic plan [] type nativeRequest
    (packProgram nativeRequest (NativeWireData.encode (.natural 7))))),
  ("different-source-receipts-remain-different-programs", nativeProgram != nativeInvalid)
]

namespace Rich
private def snapshot : Snapshot := ⟨GeneralPremise.Controls.language,
  [("a", GeneralPremise.Controls.name)], GeneralPremise.Controls.provider⟩
private def plan : Plan := compile snapshot {sites := .rootOnly, includeDerivedEquations := false}
private def source : Pattern := GeneralPremise.Controls.source [GeneralPremise.Controls.zero, GeneralPremise.Controls.zero]
private def receipts : List Proof := GeneralPremiseNativeDiscovery.heuristicReceipts
  DynamicProvider.empty plan [] GeneralPremise.Controls.term source 512

def checks : List (String × Bool) := [
  ("original-quantified-scoped-source-produces-receipts", !receipts.isEmpty),
  ("query-freshness-quantifier-scoped-child-history", receipts.all fun receipt => receipt.premiseHistory.length == 4),
  ("named-free-context-retained-in-native-proof-packet", plan.snapshot.freeTypes.length == 1),
  ("original-quantified-scoped-receipts-have-typed-programs", receipts.all fun receipt =>
    (compileProgram? scope handler DynamicProvider.empty plan [] GeneralPremise.Controls.term .nil (source, receipt.target) receipt).isSome),
  ("original-quantified-scoped-native-programs-replay", receipts.all fun receipt =>
    checkProgram scope handler DynamicProvider.empty plan [] GeneralPremise.Controls.term
      (requestAt scope handler plan [] GeneralPremise.Controls.term (source, receipt.target))
      (program scope handler plan [] GeneralPremise.Controls.term (source, receipt.target) receipt)),
  ("missing-original-quantified-history-refuses", receipts.all fun receipt =>
    !(GeneralPremiseNativeEvidence.check DynamicProvider.empty plan [] GeneralPremise.Controls.term (source, receipt.target)
      {receipt with premiseHistory := receipt.premiseHistory.take 2 ++ receipt.premiseHistory.drop 3}))
]
end Rich

namespace Rest
private def element : TypeExpr := .base "Term"
private def bag : TypeExpr := .collection .hashBag element
private def zero : Pattern := .apply "Zero" []
private def rule : RewriteRule where
  name := "consume-one-bag-element"
  typeContext := [("tail", bag)]
  left := .collection .hashBag [zero] (some "tail")
  right := .collection .hashBag [] (some "tail")
  premises := []
private def language : LanguageDef where
  name := "source-rest-receipt"
  types := ["Term"]
  terms := [{label := "Zero", category := "Term", params := [], syntaxPattern := []}]
  rewrites := [rule]
  equations := []
private def snapshot : Snapshot := ⟨language, [], ⟨[], [], []⟩⟩
private def plan : Plan := compile snapshot {sites := .rootOnly, includeDerivedEquations := false}
private def source : Pattern := .collection .hashBag [zero, zero] none
private def receipts : List Proof := GeneralPremiseNativeDiscovery.heuristicReceipts
  DynamicProvider.empty plan [] bag source 512

def checks : List (String × Bool) := [
  ("actual-raw-rest-rule-installed", plan.rules.length == 1),
  ("actual-raw-rest-source-produces-receipts", !receipts.isEmpty),
  ("original-rest-occurrence-multiplicity", receipts.length == 2),
  ("source-rest-values-have-typed-native-programs", receipts.all fun receipt =>
    (compileProgram? scope handler DynamicProvider.empty plan [] bag .nil (source, receipt.target) receipt).isSome),
  ("source-rest-values-have-original-output", receipts.all fun receipt =>
    receipt.target == .collection .hashBag [zero] none),
  ("source-rest-native-programs-replay", receipts.all fun receipt =>
    checkProgram scope handler DynamicProvider.empty plan [] bag
      (requestAt scope handler plan [] bag (source, receipt.target))
      (program scope handler plan [] bag (source, receipt.target) receipt)),
  ("source-rest-occurrences-not-collapsed", ((receipts.map fun receipt =>
    program (n := 0) scope handler plan [] bag (source, receipt.target) receipt).eraseDups).length == receipts.length)
]
end Rest

def checks : List (String × Bool) :=
  match actual? with
  | none => [("original-recursive-receipt-missing", false)]
  | some actual => checksFor actual ++ Rich.checks ++ Rest.checks

#guard checks.all Prod.snd

example : (signature scope handler dynamic plan [] type).Formed NativeWireData.rules :=
  signature_formed scope handler dynamic plan [] type

example : FormationSensitive.Typing (rules scope handler dynamic plan [] type) .nil
    (family scope handler plan [] type claim) (sortTm (.max Tower.zero Tower.zero)) :=
  family_formed scope handler dynamic plan [] type .nil claim

example (job : GeneralRuleJobs.Job) : FormationSensitive.Typing
    (rules scope handler dynamic plan [] type) .nil
    (receiptAt scope handler plan [] type {candidate job with premiseHistory := []}) NativeWireData.dataType :=
  receipt_typed scope handler dynamic plan [] type .nil _

example (job : GeneralRuleJobs.Job) :
    readProgram? scope handler dynamic plan [] type
      (requestAt scope handler plan [] type claim) (receiptAt scope handler plan [] type (candidate job)) = none := by
  simp only [readProgram?, readPacked?, receiptAt, AuthoredPremiseServices.nativeObject,
    AuthoredPremiseServices.objectWire, NativeWireData.encode, Bind.bind, Option.bind]

example (job : GeneralRuleJobs.Job) :
    program (n := 0) scope handler plan [] type claim (candidate job) ≠
      program scope handler plan [] type claim {candidate job with premiseHistory := []} := by
  intro same
  have receipt := program_injective scope handler plan [] type claim same
  have events := congrArg GeneralRuleJobs.Receipt.premiseHistory receipt
  change history 1 = [] at events
  cases events

example (job : GeneralRuleJobs.Job) :
    ∃ middle, Step (rules scope handler dynamic plan [] type).headEq
      (program (n := 0) scope handler plan [] type claim (candidate job)) middle
      (rules scope handler dynamic plan [] type).computation ∧
    Step (rules scope handler dynamic plan [] type).headEq middle
      (.pair (receiptAt scope handler plan [] type (candidate job)) (.refl (requestAt scope handler plan [] type claim)))
      (rules scope handler dynamic plan [] type).computation :=
  program_two_steps scope handler dynamic plan [] type claim (candidate job)

def run : IO Unit := do
  for (label, passed) in checks do
    if !passed then throw (IO.userError label)
    IO.println s!"PASS {label}"
  IO.println s!"{checks.length} native dependent receipt-family controls"

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredPremiseProofFamily.Controls
