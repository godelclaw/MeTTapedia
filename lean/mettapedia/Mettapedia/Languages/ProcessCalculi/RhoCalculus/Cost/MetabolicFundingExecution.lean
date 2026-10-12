import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.MetabolicStackInternalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicInitialConfiguration
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.MetabolicReflection

/-!
# Located funding receipts executed by the pure rho stack protocol

Each selected source purse has its own isolated, canonical protocol session.
The actual occurrence path performs reclaim and debit COMM, records the entire
head signature and reissues the ordered tail. Source signatures and source
owner locations remain in the dependent receipt. The two target administrative
communications are counted separately from the source's signing-atom ledger.
This construction does not assert a compiler for arbitrary cost terms or a
shared-channel composition of independently isolated sessions.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.FundingExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Canonical CanonicalBag LanguageDefGSLT ResourcePredation ResourceClaimHistory
open StackInternalization

universe u

/-- Read only actual top-level messages at the specified canonical channel. -/
def outputs (channel : Pattern) (process : RhoProcess) : Multiset Pattern :=
  (fromProcess process).1.filterMap (RhoCalculus.Metabolic.outputAt channel)

/-- The same independently defined readout on a retained occurrence endpoint. -/
def occurrenceOutputs (channel : Pattern) (configuration : Configuration) : Multiset Pattern :=
  (inventory configuration).1.filterMap (RhoCalculus.Metabolic.outputAt channel)

theorem occurrenceOutputs_readout (channel : Pattern) (configuration : Configuration) :
    occurrenceOutputs channel configuration = outputs channel (readout configuration) := by
  simp [occurrenceOutputs, outputs, readout]

private theorem outputs_parallel_cons (channel : Pattern) (first : RhoProcess)
    (rest : List RhoProcess) :
    outputs channel (RhoCalculus.Metabolic.parallel (first :: rest)) =
      outputs channel first + outputs channel (RhoCalculus.Metabolic.parallel rest) := by
  unfold outputs
  rw [RhoCalculus.Metabolic.parallel, RhoCalculus.Metabolic.parallel,
    fromProcess_ofList_inventory, fromProcess_ofList_inventory, fromProcess_inventory]
  rw [List.map_cons, List.map_cons, ← List.singleton_append, bagContents_append,
    ← Multiset.coe_add, Multiset.filterMap_add]

private theorem outputs_parallel_nil (channel : Pattern) :
    outputs channel (RhoCalculus.Metabolic.parallel []) = 0 := by
  rw [outputs, RhoCalculus.Metabolic.parallel, fromProcess_ofList_inventory]
  rfl

private theorem filterMap_singleton (read : Pattern → Option Pattern) (pattern : Pattern) :
    ({pattern} : Multiset Pattern).filterMap read =
      ((read pattern).map fun answer => ({answer} : Multiset Pattern)).getD 0 := by
  change (pattern ::ₘ 0).filterMap read = _
  rw [Multiset.filterMap_cons, Multiset.filterMap_zero, add_zero]

private theorem outputs_message {Head : Type u} (encoding : RhoCalculus.Metabolic.Encoding Head)
    (stack : RhoCalculus.Metabolic.Stack Head) :
    outputs RhoCalculus.Metabolic.metabolic (RhoCalculus.Metabolic.messageProcess encoding stack) =
      {canonicalize (RhoCalculus.Metabolic.payload encoding stack)} ∧
    outputs RhoCalculus.Metabolic.spent (RhoCalculus.Metabolic.messageProcess encoding stack) = 0 := by
  simp [outputs, fromProcess_inventory, RhoCalculus.Metabolic.messageProcess,
    RhoCalculus.Metabolic.closedProcess, RhoCalculus.Metabolic.message, CanonicalReaction.output,
    canonicalize, canonicalizeList, normalizeQuote, bagContents, bagSplice, filterMap_singleton,
    RhoCalculus.Metabolic.outputAt, RhoCalculus.Metabolic.metabolic, RhoCalculus.Metabolic.spent,
    RhoCalculus.Metabolic.pop, RhoCalculus.Metabolic.zero]

private theorem outputs_burned {Head : Type u} (encoding : RhoCalculus.Metabolic.Encoding Head)
    (head : Head) :
    outputs RhoCalculus.Metabolic.metabolic (RhoCalculus.Metabolic.burnedProcess encoding head) = 0 ∧
      outputs RhoCalculus.Metabolic.spent (RhoCalculus.Metabolic.burnedProcess encoding head) = {encoding.code head} := by
  simp [outputs, fromProcess_inventory, RhoCalculus.Metabolic.burnedProcess,
    RhoCalculus.Metabolic.closedProcess, RhoCalculus.Metabolic.burned, CanonicalReaction.output,
    canonicalize, canonicalizeList, normalizeQuote, bagContents, bagSplice, encoding.canonical, filterMap_singleton,
    RhoCalculus.Metabolic.outputAt, RhoCalculus.Metabolic.metabolic, RhoCalculus.Metabolic.spent,
    RhoCalculus.Metabolic.pop, RhoCalculus.Metabolic.zero]

private theorem outputs_owner (channel : Pattern) (count : Nat) :
    outputs channel (RhoCalculus.Metabolic.ownerProcess count) = 0 := by
  cases count <;>
    simp [outputs, fromProcess_inventory, RhoCalculus.Metabolic.ownerProcess,
      RhoCalculus.Metabolic.closedProcess, RhoCalculus.Metabolic.owner, CanonicalReaction.input,
      canonicalize, canonicalizeList, bagContents, bagSplice, filterMap_singleton, RhoCalculus.Metabolic.outputAt,
      RhoCalculus.Metabolic.zero]

theorem live_outputs {Head : Type u} (encoding : RhoCalculus.Metabolic.Encoding Head)
    (stack : RhoCalculus.Metabolic.Stack Head) (count : Nat) (record : List Head) :
    outputs RhoCalculus.Metabolic.metabolic (RhoCalculus.Metabolic.live encoding stack count record) =
      {canonicalize (RhoCalculus.Metabolic.payload encoding stack)} ∧
      outputs RhoCalculus.Metabolic.spent (RhoCalculus.Metabolic.live encoding stack count record) =
        (record.map encoding.code : Multiset Pattern) := by
  have records :
      outputs RhoCalculus.Metabolic.metabolic
        (RhoCalculus.Metabolic.parallel (record.map (RhoCalculus.Metabolic.burnedProcess encoding))) = 0 ∧
      outputs RhoCalculus.Metabolic.spent
        (RhoCalculus.Metabolic.parallel (record.map (RhoCalculus.Metabolic.burnedProcess encoding))) =
          (record.map encoding.code : Multiset Pattern) := by
    induction record with
    | nil => simp [outputs_parallel_nil]
    | cons head rest ih =>
        constructor
        · simp [outputs_parallel_cons, (outputs_burned encoding head).1, ih.1]
        · simp [outputs_parallel_cons, (outputs_burned encoding head).2, ih.2]
  constructor <;>
    simp only [RhoCalculus.Metabolic.live, List.cons_append, List.nil_append,
      outputs_parallel_cons, (outputs_message encoding stack).1, (outputs_message encoding stack).2,
      outputs_owner, records.1, records.2, zero_add, add_zero]

variable {Ground : Type u} [Encodable Ground]
variable {location : CostName Ground} {demand : CostSig Ground}
variable {available residual : Multiset (LocatedPurse Ground)}

def tail (debit : DebitReadout Ground) : TargetStack Ground :=
  stack (CostStack.ofList debit.tail)

/-- The message, finite controller and existing spent records are all present
before execution. Every initial prime has an actual fresh occurrence key. -/
def initial (debit : DebitReadout Ground) (count : Nat) (record : List (CostSig Ground)) : Configuration :=
  RhoCalculus.Metabolic.annotate
    (RhoCalculus.Metabolic.live signatureEncoding (.cell debit.head (tail debit)) (count + 1) record)
    (fun _ => .computation) 0

theorem initial_inventory (debit : DebitReadout Ground) (count : Nat) (record : List (CostSig Ground)) :
    inventory (initial debit count record) =
      fromProcess (RhoCalculus.Metabolic.live signatureEncoding (.cell debit.head (tail debit))
        (count + 1) record) :=
  RhoCalculus.Metabolic.annotate_inventory _ _ _

theorem initial_distinct (debit : DebitReadout Ground) (count : Nat) (record : List (CostSig Ground)) :
    Distinct (initial debit count record) :=
  RhoCalculus.Metabolic.annotate_distinct _ _ _

/-- Both the actual source selection and the complete pure-rho execution are
retained. The nominal owner location is not inferred from a target channel. -/
structure SelectedReceipt (cover : LocatedTokenCover location demand available residual)
    (count : Nat) (record : List (CostSig Ground)) where
  debit : DebitReadout Ground
  selected : debit ∈ FundingReadout.debits cover
  actual : RhoCalculus.Metabolic.Cycle signatureEncoding debit.head (tail debit) count record
    (initial debit count record)

def execute (cover : LocatedTokenCover location demand available residual)
    (debit : DebitReadout Ground) (selected : debit ∈ FundingReadout.debits cover)
    (count : Nat) (record : List (CostSig Ground)) : SelectedReceipt cover count record where
  debit := debit
  selected := selected
  actual := RhoCalculus.Metabolic.cycle signatureEncoding debit.head (tail debit)
    count record (initial debit count record) (initial_inventory _ _ _)

namespace SelectedReceipt

variable {cover : LocatedTokenCover location demand available residual}
variable {count : Nat} {record : List (CostSig Ground)}

theorem source_owned (receipt : SelectedReceipt cover count record) :
    receipt.debit.before.toPurse ∈ available ∧ receipt.debit.after.toPurse ∈ residual :=
  FundingReadout.selected_occurrence_owned cover receipt.selected

theorem owner_location (receipt : SelectedReceipt cover count record) :
    receipt.debit.location = location := FundingReadout.debit_location cover receipt.selected

theorem initial_message (receipt : SelectedReceipt cover count record) :
    occurrenceOutputs RhoCalculus.Metabolic.metabolic (initial receipt.debit count record) =
      {canonicalize (payload receipt.debit.before.toPurse.stack)} := by
  change ((inventory _).1).filterMap _ = _
  rw [initial_inventory]
  exact (live_outputs signatureEncoding (.cell receipt.debit.head (tail receipt.debit))
    (count + 1) record).1

theorem remaining_message (receipt : SelectedReceipt cover count record) :
    occurrenceOutputs RhoCalculus.Metabolic.metabolic receipt.actual.pop.target =
      {canonicalize (payload receipt.debit.after.toPurse.stack)} := by
  change ((inventory _).1).filterMap _ = _
  rw [receipt.actual.remaining]
  exact (live_outputs signatureEncoding (tail receipt.debit) count (receipt.debit.head :: record)).1

/-- Complete heads are read from the actual emitted spent messages, preserving
the multiplicity of prior records and of repeated signing atoms. -/
theorem spent_messages (receipt : SelectedReceipt cover count record) :
    occurrenceOutputs RhoCalculus.Metabolic.spent receipt.actual.pop.target =
      ((receipt.debit.head :: record).map signatureEncoding.code : Multiset Pattern) := by
  change ((inventory _).1).filterMap _ = _
  rw [receipt.actual.remaining]
  exact (live_outputs signatureEncoding (tail receipt.debit) count (receipt.debit.head :: record)).2

theorem spent_signature_readout (receipt : SelectedReceipt cover count record) :
    (occurrenceOutputs RhoCalculus.Metabolic.spent receipt.actual.pop.target).map
        (SignatureCodec.signatureRead (Ground := Ground)) =
      (receipt.debit.head :: record : Multiset (CostSig Ground)) := by
  rw [spent_messages]
  simp [List.map_map, Function.comp_def, signatureEncoding, SignatureCodec.signature_roundtrip]

def spentLedger (receipt : SelectedReceipt cover count record) : CostSig Ground :=
  ((occurrenceOutputs RhoCalculus.Metabolic.spent receipt.actual.pop.target).map
    (SignatureCodec.signatureRead (Ground := Ground))).sum

theorem spent_ledger (receipt : SelectedReceipt cover count record) :
    receipt.spentLedger = receipt.debit.head + record.sum := by
  rw [spentLedger, spent_signature_readout]
  simp

theorem complete_tail_readout (receipt : SelectedReceipt cover count record) :
    ∃ emitted ∈ occurrenceOutputs RhoCalculus.Metabolic.metabolic receipt.actual.pop.target,
      RhoCalculus.Metabolic.CanonicalPayloadReadout emitted
        (receipt.debit.tail.map signatureEncoding.code) ∧
      (receipt.debit.tail.map signatureEncoding.code).map
        (SignatureCodec.signatureRead (Ground := Ground)) = receipt.debit.tail := by
  refine ⟨canonicalize (payload receipt.debit.after.toPurse.stack), ?_, ?_, ?_⟩
  · rw [remaining_message]
    simp
  · have actual := RhoCalculus.Metabolic.canonical_payload_readout signatureEncoding (tail receipt.debit)
    simpa [tail, DebitReadout.after, StackReadout.toPurse, ordered_heads, payload] using actual
  · simp [List.map_map, Function.comp_def, signatureEncoding, SignatureCodec.signature_roundtrip]

theorem administrative_count (receipt : SelectedReceipt cover count record) :
    receipt.actual.execution.length = 2 := receipt.actual.execution_length

theorem actual_public_path (receipt : SelectedReceipt cover count record) :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout (initial receipt.debit count record))
      (readout receipt.actual.pop.target) := receipt.actual.actual_public_path

theorem every_supplied_execution_bounded (receipt : SelectedReceipt cover count record)
    {target : Configuration} (execution : Execution (initial receipt.debit count record) target) :
    execution.length ≤ 2 * (count + 1) :=
  RhoCalculus.Metabolic.live_execution_length_bound signatureEncoding (count + 1)
    (.cell receipt.debit.head (tail receipt.debit)) record _ _ (initial_inventory _ _ _) execution

theorem exclusive_claims (receipt : SelectedReceipt cover count record) :
    receipt.actual.execution.claimedKeys.Nodup :=
  receipt.actual.execution.claimedKeys_nodup (initial_distinct _ _ _)

theorem complete_ledger (receipt : SelectedReceipt cover count record) :
    receipt.debit.before.inventory = receipt.debit.after.inventory + receipt.debit.head :=
  receipt.debit.signature_balance

theorem strictly_positive_burn (receipt : SelectedReceipt cover count record) :
    0 < receipt.debit.head.card := Multiset.card_pos.mpr receipt.debit.head_valid

end SelectedReceipt

/-- A finite family of isolated session receipts, indexed by actual selected
purse occurrences. It is not a claim that sessions sharing these fixed names
may be freely combined in one parallel runtime. -/
def all (cover : LocatedTokenCover location demand available residual) :
    Multiset (SelectedReceipt cover 0 []) :=
  (FundingReadout.debits cover).attach.map fun selected => execute cover selected.1 selected.2 0 []

theorem all_debit_projection (cover : LocatedTokenCover location demand available residual) :
    (all cover).map SelectedReceipt.debit = FundingReadout.debits cover := by
  simp [all, execute, Multiset.map_map]

theorem all_card (cover : LocatedTokenCover location demand available residual) :
    (all cover).card = cover.chosen.card := by
  simp [all, FundingReadout.debit_card]

theorem all_before_messages (cover : LocatedTokenCover location demand available residual) :
    (all cover).map (fun receipt => receipt.debit.before) + FundingReadout.messages cover.untouched =
      FundingReadout.messages available := by
  have mapped := congrArg (Multiset.map DebitReadout.before) (all_debit_projection cover)
  rw [Multiset.map_map] at mapped
  exact (congrArg (· + FundingReadout.messages cover.untouched) mapped).trans
    (FundingReadout.available_messages cover).symm

theorem all_after_messages (cover : LocatedTokenCover location demand available residual) :
    (all cover).map (fun receipt => receipt.debit.after) + FundingReadout.messages cover.untouched =
      FundingReadout.messages residual := by
  have mapped := congrArg (Multiset.map DebitReadout.after) (all_debit_projection cover)
  rw [Multiset.map_map] at mapped
  exact (congrArg (· + FundingReadout.messages cover.untouched) mapped).trans
    (FundingReadout.residual_messages cover).symm

theorem all_consumed_signature (cover : LocatedTokenCover location demand available residual) :
    ((all cover).map (fun receipt => receipt.debit.head)).sum = demand := by
  have mapped := congrArg (Multiset.map DebitReadout.head) (all_debit_projection cover)
  rw [Multiset.map_map] at mapped
  exact (congrArg Multiset.sum mapped).trans (FundingReadout.consumed_heads cover)

/-- The ledger recovered from actual emitted spent messages is the complete
source demand, rather than a separate predicted charge. -/
theorem all_emitted_signature (cover : LocatedTokenCover location demand available residual) :
    ((all cover).map SelectedReceipt.spentLedger).sum = demand := by
  have actual : (all cover).map SelectedReceipt.spentLedger =
      (all cover).map (fun receipt => receipt.debit.head) := by
    apply Multiset.map_congr rfl
    intro receipt _
    simpa using receipt.spent_ledger
  rw [actual, all_consumed_signature]

theorem all_administrative_count (cover : LocatedTokenCover location demand available residual) :
    ((all cover).map (fun receipt => receipt.actual.execution.length)).sum = 2 * cover.chosen.card := by
  have counts : (all cover).map (fun receipt => receipt.actual.execution.length) =
      (all cover).map (fun _ => 2) := by
    apply Multiset.map_congr rfl
    intro receipt _
    exact receipt.administrative_count
  rw [counts]
  simp [all_card, Nat.mul_comm]

theorem all_strict_burn (cover : LocatedTokenCover location demand available residual)
    (valid : demand.RuntimeValid) :
    0 < (((all cover).map (fun receipt : SelectedReceipt cover 0 [] => receipt.debit.head)).sum).card := by
  rw [all_consumed_signature]
  exact Multiset.card_pos.mpr valid

/-- A finite ordered prefix is represented before execution, with the complete
finite controller present from the start. -/
def prefixInitial (consumed suffix : CostStack Ground) (record : List (CostSig Ground)) : Configuration :=
  RhoCalculus.Metabolic.annotate
    (RhoCalculus.Metabolic.live signatureEncoding ((stack consumed).append (stack suffix))
      (stack consumed).size record) (fun _ => .computation) 0

def executePrefix (consumed suffix : CostStack Ground) (record : List (CostSig Ground)) :
    RhoCalculus.Metabolic.Batch signatureEncoding (stack consumed) (stack suffix) record
      (prefixInitial consumed suffix record) :=
  RhoCalculus.Metabolic.batch signatureEncoding (stack consumed) (stack suffix) record
    (prefixInitial consumed suffix record) (RhoCalculus.Metabolic.annotate_inventory _ _ _)

theorem prefix_administrative_count (consumed suffix : CostStack Ground) (record : List (CostSig Ground)) :
    (executePrefix consumed suffix record).execution.length = 2 * consumed.cellCount := by
  rw [(executePrefix consumed suffix record).length, exact_cells]

theorem prefix_actual_public_path (consumed suffix : CostStack Ground) (record : List (CostSig Ground)) :
    Relation.ReflTransGen rhoLanguageDefGSLT.Step (readout (prefixInitial consumed suffix record))
      (readout (executePrefix consumed suffix record).target) :=
  (executePrefix consumed suffix record).execution.public_history

theorem prefix_remaining_message (consumed suffix : CostStack Ground) (record : List (CostSig Ground)) :
    occurrenceOutputs RhoCalculus.Metabolic.metabolic (executePrefix consumed suffix record).target =
      {canonicalize (payload suffix)} := by
  change ((inventory _).1).filterMap _ = _
  rw [(executePrefix consumed suffix record).remaining]
  exact (live_outputs signatureEncoding (stack suffix) 0 ((stack consumed).heads.reverse ++ record)).1

theorem prefix_spent_signature_readout (consumed suffix : CostStack Ground) (record : List (CostSig Ground)) :
    (occurrenceOutputs RhoCalculus.Metabolic.spent (executePrefix consumed suffix record).target).map
        (SignatureCodec.signatureRead (Ground := Ground)) =
      (consumed.toList.reverse ++ record : Multiset (CostSig Ground)) := by
  change ((((inventory _).1).filterMap _).map _) = _
  rw [(executePrefix consumed suffix record).remaining]
  change (outputs RhoCalculus.Metabolic.spent
    (RhoCalculus.Metabolic.live signatureEncoding (stack suffix) 0
      ((stack consumed).heads.reverse ++ record))).map SignatureCodec.signatureRead = _
  rw [(live_outputs signatureEncoding (stack suffix) 0
    ((stack consumed).heads.reverse ++ record)).2, ordered_heads]
  simp [List.map_map, Function.comp_def, signatureEncoding, SignatureCodec.signature_roundtrip]

theorem prefix_spent_ledger (consumed suffix : CostStack Ground) (record : List (CostSig Ground)) :
    ((occurrenceOutputs RhoCalculus.Metabolic.spent (executePrefix consumed suffix record).target).map
      (SignatureCodec.signatureRead (Ground := Ground))).sum =
      consumed.storedSignatures + record.sum := by
  rw [prefix_spent_signature_readout]
  simp [← CostStack.storedSignatures_eq_sum]

namespace Controls

def triple : DebitReadout Nat :=
  ⟨.signature {7}, {0, 0, 0}, [{1}], by simp [CostSig.RuntimeValid]⟩

def tripleAvailable : Multiset (LocatedPurse Nat) := {triple.before.toPurse}
def tripleResidual : Multiset (LocatedPurse Nat) := {triple.after.toPurse}

def tripleCover : LocatedTokenCover triple.location triple.head tripleAvailable tripleResidual where
  chosen := {⟨triple.head, CostStack.ofList triple.tail, triple.head_valid⟩}
  untouched := 0
  available_eq := by simp [tripleAvailable, triple, DebitReadout.before, StackReadout.toPurse, CostStack.ofList]
  residual_eq := by simp [tripleResidual, triple, DebitReadout.after, StackReadout.toPurse]
  demand_eq := by simp

def tripleReceipt : SelectedReceipt tripleCover 0 [] :=
  execute tripleCover triple (by simp [FundingReadout.debits, tripleCover, triple]) 0 []

theorem atom_burn_and_communication_counts_are_distinct :
    tripleReceipt.debit.head.card = 3 ∧ tripleReceipt.actual.execution.length = 2 := by
  constructor
  · simp [tripleReceipt, execute, triple]
  · exact tripleReceipt.administrative_count

theorem actual_spent_message_retains_all_three_atoms :
    tripleReceipt.spentLedger = {0, 0, 0} := by
  simpa [tripleReceipt, execute, triple] using tripleReceipt.spent_ledger

theorem ordered_tail_is_actually_reissued :
    ∃ emitted ∈ occurrenceOutputs RhoCalculus.Metabolic.metabolic tripleReceipt.actual.pop.target,
      RhoCalculus.Metabolic.CanonicalPayloadReadout emitted
        (([{1}] : List (CostSig Nat)).map signatureEncoding.code) := by
  obtain ⟨emitted, sent, read, _⟩ := tripleReceipt.complete_tail_readout
  exact ⟨emitted, sent, read⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic.FundingExecution
