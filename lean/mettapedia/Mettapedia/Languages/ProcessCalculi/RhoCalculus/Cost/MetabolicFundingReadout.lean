import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Located
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation
import Mathlib.Data.Multiset.Filter

/-!
# Ordered located-stack readouts of actual funding covers

The source receipt supplies the exact chosen purse occurrences. The readout
retains every signing atom, every cell in tail order, and the nominal location.
No scalar purse is substituted for this information. Numerical burn is a
derived observation of the same consumed signatures.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic

universe u

/-- The data carried by one located stack message before rho lowering. -/
structure StackReadout (Ground : Type u) where
  location : CostName Ground
  cells : List (CostSig Ground)
  deriving DecidableEq

namespace StackReadout

def ofPurse {Ground : Type u} (purse : LocatedPurse Ground) : StackReadout Ground :=
  ⟨purse.location, purse.stack.toList⟩

def toPurse {Ground : Type u} (message : StackReadout Ground) : LocatedPurse Ground :=
  ⟨message.location, CostStack.ofList message.cells⟩

@[simp]
theorem toPurse_ofPurse {Ground : Type u} (purse : LocatedPurse Ground) :
    (ofPurse purse).toPurse = purse := by
  cases purse
  simp [ofPurse, toPurse]

@[simp]
theorem ofPurse_toPurse {Ground : Type u} (message : StackReadout Ground) :
    ofPurse message.toPurse = message := by
  cases message
  simp [ofPurse, toPurse]

theorem ofPurse_injective {Ground : Type u} :
    Function.Injective (ofPurse (Ground := Ground)) := by
  intro first second equality
  simpa using congrArg toPurse equality

def inventory {Ground : Type u} (message : StackReadout Ground) : CostSig Ground :=
  message.cells.sum

@[simp]
theorem inventory_ofPurse {Ground : Type u} (purse : LocatedPurse Ground) :
    (ofPurse purse).inventory = purse.stack.storedSignatures :=
  (CostStack.storedSignatures_eq_sum purse.stack).symm

end StackReadout

/-- One selected head and its ordered surviving tail, at their actual location. -/
structure DebitReadout (Ground : Type u) where
  location : CostName Ground
  head : CostSig Ground
  tail : List (CostSig Ground)
  head_valid : head.RuntimeValid

namespace DebitReadout

def before {Ground : Type u} (debit : DebitReadout Ground) : StackReadout Ground :=
  ⟨debit.location, debit.head :: debit.tail⟩

def after {Ground : Type u} (debit : DebitReadout Ground) : StackReadout Ground :=
  ⟨debit.location, debit.tail⟩

theorem ordered_tail {Ground : Type u} (debit : DebitReadout Ground) :
    debit.before.cells = debit.head :: debit.after.cells := rfl

theorem same_location {Ground : Type u} (debit : DebitReadout Ground) :
    debit.before.location = debit.after.location := rfl

theorem signature_balance {Ground : Type u} (debit : DebitReadout Ground) :
    debit.before.inventory = debit.after.inventory + debit.head := by
  simp [before, after, StackReadout.inventory, add_comm]

end DebitReadout

namespace FundingReadout

variable {Ground : Type u} {location : CostName Ground} {demand : CostSig Ground}
  {available residual : Multiset (LocatedPurse Ground)}

def debits (cover : LocatedTokenCover location demand available residual) :
    Multiset (DebitReadout Ground) :=
  cover.chosen.map fun choice => ⟨location, choice.head, choice.tail.toList, choice.head_valid⟩

def messages (purses : Multiset (LocatedPurse Ground)) : Multiset (StackReadout Ground) :=
  purses.map StackReadout.ofPurse

theorem selected_before (cover : LocatedTokenCover location demand available residual) :
    messages cover.selectedBefore = (debits cover).map DebitReadout.before := by
  simp [messages, LocatedTokenCover.selectedBefore, debits, StackReadout.ofPurse,
    DebitReadout.before, CostStack.toList, Function.comp_def]

theorem selected_after (cover : LocatedTokenCover location demand available residual) :
    messages cover.selectedAfter = (debits cover).map DebitReadout.after := by
  simp [messages, LocatedTokenCover.selectedAfter, debits, StackReadout.ofPurse,
    DebitReadout.after, Function.comp_def]

/-- The target-facing message data comes from the actual available occurrences. -/
theorem available_messages (cover : LocatedTokenCover location demand available residual) :
    messages available = (debits cover).map DebitReadout.before + messages cover.untouched := by
  calc
    messages available = messages (cover.selectedBefore + cover.untouched) :=
      congrArg messages cover.available_decomposition
    _ = (debits cover).map DebitReadout.before + messages cover.untouched := by
      rw [messages, Multiset.map_add]
      exact congrArg (· + _) (selected_before cover)

theorem residual_messages (cover : LocatedTokenCover location demand available residual) :
    messages residual = (debits cover).map DebitReadout.after + messages cover.untouched := by
  calc
    messages residual = messages (cover.selectedAfter + cover.untouched) :=
      congrArg messages cover.residual_decomposition
    _ = (debits cover).map DebitReadout.after + messages cover.untouched := by
      rw [messages, Multiset.map_add]
      exact congrArg (· + _) (selected_after cover)

/-- Recovering the source purses preserves all occurrences, including duplicates. -/
theorem source_roundtrip (purses : Multiset (LocatedPurse Ground)) :
    (messages purses).map StackReadout.toPurse = purses := by
  simp [messages]

theorem occurrence_multiplicity [DecidableEq Ground]
    (purses : Multiset (LocatedPurse Ground)) (purse : LocatedPurse Ground) :
    (messages purses).count (StackReadout.ofPurse purse) = purses.count purse :=
  Multiset.count_map_eq_count' _ _ StackReadout.ofPurse_injective _

theorem debit_card (cover : LocatedTokenCover location demand available residual) :
    (debits cover).card = cover.chosen.card := by
  simp [debits]

/-- This ledger is the complete consumed signature, before any price valuation. -/
theorem consumed_heads (cover : LocatedTokenCover location demand available residual) :
    ((debits cover).map DebitReadout.head).sum = demand := by
  simpa [debits] using cover.demand_eq.symm

theorem exact_receipt_ledger (cover : LocatedTokenCover location demand available residual) :
    ((debits cover).map DebitReadout.head).sum =
      (cover.fundingContributions.map FundingContribution.spend).sum := by
  rw [consumed_heads, cover.funding_contributions_eq_selected_heads]

theorem debit_location (cover : LocatedTokenCover location demand available residual)
    {debit : DebitReadout Ground} (member : debit ∈ debits cover) :
    debit.location = location := by
  obtain ⟨choice, _, rfl⟩ := Multiset.mem_map.mp member
  rfl

theorem selected_occurrence_owned (cover : LocatedTokenCover location demand available residual)
    {debit : DebitReadout Ground} (member : debit ∈ debits cover) :
    debit.before.toPurse ∈ available ∧ debit.after.toPurse ∈ residual := by
  change debit ∈ cover.chosen.map
    (fun choice => (⟨location, choice.head, choice.tail.toList, choice.head_valid⟩ : DebitReadout Ground)) at member
  obtain ⟨choice, chosen, rfl⟩ := Multiset.mem_map.mp member
  constructor
  · rw [cover.available_decomposition]
    apply Multiset.mem_add.mpr
    left
    exact Multiset.mem_map.mpr ⟨choice, chosen, by simp [StackReadout.toPurse,
      DebitReadout.before, CostStack.ofList]⟩
  · rw [cover.residual_decomposition]
    apply Multiset.mem_add.mpr
    left
    exact Multiset.mem_map.mpr ⟨choice, chosen, by simp [StackReadout.toPurse,
      DebitReadout.after]⟩

/-- Funding retains the entire multiset of nominal locations. -/
theorem locations_preserved (cover : LocatedTokenCover location demand available residual) :
    available.map LocatedPurse.location = residual.map LocatedPurse.location := by
  calc
    available.map LocatedPurse.location =
        (cover.selectedBefore + cover.untouched).map LocatedPurse.location :=
      congrArg (Multiset.map LocatedPurse.location) cover.available_decomposition
    _ = (cover.selectedAfter + cover.untouched).map LocatedPurse.location := by
      simp [LocatedTokenCover.selectedBefore, LocatedTokenCover.selectedAfter]
    _ = residual.map LocatedPurse.location :=
      (congrArg (Multiset.map LocatedPurse.location) cover.residual_decomposition).symm

/-- Purses at every other location remain unchanged, not merely equal in number. -/
theorem other_locations_preserved [DecidableEq Ground]
    (cover : LocatedTokenCover location demand available residual) :
    (available.filter fun purse => purse.location ≠ location) =
      (residual.filter fun purse => purse.location ≠ location) := by
  calc
    (available.filter fun purse => purse.location ≠ location) =
        (cover.selectedBefore + cover.untouched).filter (fun purse => purse.location ≠ location) :=
      congrArg (Multiset.filter fun purse => purse.location ≠ location) cover.available_decomposition
    _ = (cover.selectedAfter + cover.untouched).filter (fun purse => purse.location ≠ location) := by
      simp [LocatedTokenCover.selectedBefore, LocatedTokenCover.selectedAfter, Multiset.filter_map]
    _ = residual.filter (fun purse => purse.location ≠ location) :=
      (congrArg (Multiset.filter fun purse => purse.location ≠ location) cover.residual_decomposition).symm

theorem stored_signature_balance (cover : LocatedTokenCover location demand available residual) :
    ((messages available).map StackReadout.inventory).sum =
      ((messages residual).map StackReadout.inventory).sum + demand := by
  simpa [messages] using cover.stored_signatures_balance

/-- A unit-per-atom account is only a projection of the complete signature receipt. -/
def burn (cover : LocatedTokenCover location demand available residual) : Nat :=
  (((debits cover).map DebitReadout.head).sum).card

@[simp]
theorem burn_eq (cover : LocatedTokenCover location demand available residual) :
    burn cover = demand.card := by
  rw [burn, consumed_heads]

theorem strict_burn (cover : LocatedTokenCover location demand available residual)
    (valid : demand.RuntimeValid) : 0 < burn cover := by
  rw [burn_eq]
  exact Multiset.card_pos.mpr valid

theorem debit_nonempty (cover : LocatedTokenCover location demand available residual)
    (valid : demand.RuntimeValid) : 0 < (debits cover).card := by
  rw [debit_card]
  exact cover.selected_card_pos valid

theorem signature_balance_card (cover : LocatedTokenCover location demand available residual) :
    (((messages available).map StackReadout.inventory).sum).card =
      (((messages residual).map StackReadout.inventory).sum).card + burn cover := by
  rw [stored_signature_balance cover, Multiset.card_add, burn_eq cover]

end FundingReadout

/-- In the actual separated source semantics, funding cannot move a purse to
another nominal owner location. Empty purses remain present in this inventory. -/
theorem source_firing_locations_preserved {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {demand : CostSig Ground}
    (step : CostStep source location demand target) (separated : source.ResourceSeparated) :
    source.purses.map Prod.fst = target.purses.map Prod.fst := by
  classical
  obtain ⟨entry, rfl, rfl, enabled, rfl⟩ := costStep_iff_exists_enabled_resource.mp step
  change (Σ location : CostName Ground, {event : CostedEvent Ground // event.location = location}) at entry
  obtain ⟨others, before, after⟩ := costResource_fire_purses_frame source entry.2 enabled
  have released := entry.2.val.contractum_purses_eq_zero separated
    (((costResource_enables_iff_le source entry.2).mp enabled).1.trans (Multiset.filter_le _ _))
  rw [after, released, add_zero, before]
  simp

/-- Every complete remote purse, including ordered contents, is unchanged by
a firing whose funding location differs from it. -/
theorem source_remote_purses_preserved {Ground : Type u} [DecidableEq Ground]
    {source target : CostConfig Ground} {location : CostName Ground} {demand : CostSig Ground}
    (step : CostStep source location demand target) (separated : source.ResourceSeparated) :
    (source.purses.filter fun purse => purse.1 ≠ location) =
      (target.purses.filter fun purse => purse.1 ≠ location) := by
  classical
  obtain ⟨entry, rfl, rfl, enabled, rfl⟩ := costStep_iff_exists_enabled_resource.mp step
  change (Σ location : CostName Ground, {event : CostedEvent Ground // event.location = location}) at entry
  obtain ⟨others, before, after⟩ := costResource_fire_purses_frame source entry.2 enabled
  have released := entry.2.val.contractum_purses_eq_zero separated
    (((costResource_enables_iff_le source entry.2).mp enabled).1.trans (Multiset.filter_le _ _))
  rw [after, released, add_zero, before]
  simp [Multiset.filter_map]

theorem source_path_locations_preserved {Ground : Type u}
    {source target : CostConfig Ground} (path : CostStepPath source target)
    (separated : source.ResourceSeparated) :
    source.purses.map Prod.fst = target.purses.map Prod.fst := by
  induction path with
  | done => rfl
  | fire step rest ih =>
      exact (source_firing_locations_preserved step separated).trans
        (ih (step.preserves_resourceSeparated separated))

namespace Controls

def repeatedHead : SelectedPurseHead Nat :=
  ⟨{0, 0}, .cons {1} .empty, by simp [CostSig.RuntimeValid]⟩

def repeatedChoices : Multiset (SelectedPurseHead Nat) := {repeatedHead, repeatedHead}

def ownerLocation : CostName Nat := .signature {7}
def remoteLocation : CostName Nat := .signature {8}

def remotePurse : LocatedPurse Nat := ⟨remoteLocation, .cons {9} (.cons {10} .empty)⟩

def before : Multiset (LocatedPurse Nat) :=
  repeatedChoices.map (fun choice => ⟨ownerLocation, .cons choice.head choice.tail⟩) + {remotePurse}

def after : Multiset (LocatedPurse Nat) :=
  repeatedChoices.map (fun choice => ⟨ownerLocation, choice.tail⟩) + {remotePurse}

def receipt : LocatedTokenCover ownerLocation ((repeatedChoices.map SelectedPurseHead.head).sum)
    before after where
  chosen := repeatedChoices
  untouched := {remotePurse}
  available_eq := rfl
  residual_eq := rfl
  demand_eq := rfl

theorem complete_duplicate_burn : FundingReadout.burn receipt = 4 := by
  rw [FundingReadout.burn_eq receipt]
  simp [repeatedChoices, repeatedHead]

theorem duplicate_receipts_retained : (FundingReadout.debits receipt).card = 2 := by
  simp [FundingReadout.debit_card, receipt, repeatedChoices]

theorem ordered_remote_tail_retained :
    StackReadout.ofPurse remotePurse ∈ FundingReadout.messages after ∧
      (StackReadout.ofPurse remotePurse).cells = [{9}, {10}] := by
  constructor
  · exact Multiset.mem_map.mpr ⟨remotePurse, by simp [after], rfl⟩
  · rfl

theorem wrong_location_excluded : remotePurse ∉ receipt.selectedBefore := by
  apply receipt.wrong_location_not_selected
  decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Metabolic
