import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileBatches
import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileCoverage

/-!
# Runtime and independent binder-family semantics

Whole finite-provider snapshots are compared to the independently defined
equation generators and primitive firings. Successful-result positions are
kept distinct from original provider-row positions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Engine
open ScopedEquationExecution (Orientation)
open Mettapedia.GSLT.LanguageDef.WellSorted
open ConditionalEquationExecution

theorem expectedReceipts_member_target (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (phase : Phase) (receipt : Receipt)
    (member : receipt ∈ expectedReceipts allowed ambient index token phase) :
    receipt.target = (⟨phase, index, token⟩ : State ambient).pattern := by
  obtain ⟨row, _, represented⟩ := List.mem_map.mp member
  cases represented
  rfl

theorem expectedReceipts_inhabited (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (phase : Phase) :
    (∃ receipt, receipt ∈ expectedReceipts allowed ambient index token phase) ↔
      token ∈ allowed := by
  constructor
  · rintro ⟨receipt, member⟩
    obtain ⟨⟨key, ordinal⟩, rowMember, _⟩ := List.mem_map.mp member
    have position := List.mk_mem_zipIdx_iff_getElem?.mp rowMember
    have enabled := List.mem_filter.mp (List.mem_of_getElem? position)
    have equal : key = token := by simpa using enabled.2
    exact equal ▸ enabled.1
  · intro enabled
    have member : token ∈ allowed.filter (fun key => key == token) := by
      simp [enabled]
    obtain ⟨ordinal, position⟩ := List.mem_iff_getElem?.mp member
    refine ⟨expectedReceipt ambient index token phase ordinal, List.mem_map.mpr ?_⟩
    exact ⟨(token, ordinal), List.mk_mem_zipIdx_iff_getElem?.mpr position, rfl⟩

theorem expectedReceipts_targets (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (phase : Phase) (target : Pattern) :
    (∃ receipt, receipt ∈ expectedReceipts allowed ambient index token phase ∧
      target = receipt.target) ↔
        token ∈ allowed ∧ target = (⟨phase, index, token⟩ : State ambient).pattern := by
  constructor
  · rintro ⟨receipt, member, equal⟩
    exact ⟨(expectedReceipts_inhabited allowed ambient index token phase).mp
      ⟨receipt, member⟩, equal.trans
        (expectedReceipts_member_target allowed ambient index token phase receipt member)⟩
  · rintro ⟨enabled, equal⟩
    obtain ⟨receipt, member⟩ :=
      (expectedReceipts_inhabited allowed ambient index token phase).mpr enabled
    exact ⟨receipt, member, equal.trans
      (expectedReceipts_member_target allowed ambient index token phase receipt member).symm⟩

theorem expectedEquationTargets_spec (allowed : List Token) (ambient : Nat)
    (source : State ambient) (equationIndex : Nat) (orientation : Orientation)
    (target : Pattern) :
    (∃ receipt, (receipt, target) ∈
      (expectedEquationReceipts allowed ambient source equationIndex orientation).map
        (fun receipt => (receipt, receipt.target))) ↔
      source.phase = equationSourcePhase orientation ∧ source.key ∈ allowed ∧
        target = (⟨equationTargetPhase orientation, source.name, source.key⟩ : State ambient).pattern := by
  by_cases active : source.phase = equationSourcePhase orientation
  · simp only [expectedEquationReceipts, active, if_true, true_and, List.map_map,
      List.mem_map]
    constructor
    · rintro ⟨_, receipt, member, equal⟩
      have targetEqual := (congrArg Prod.snd equal).symm
      exact (expectedReceipts_targets allowed ambient source.name source.key
        (equationTargetPhase orientation) target).mp ⟨receipt, member, targetEqual⟩
    · intro admitted
      obtain ⟨receipt, member, targetEqual⟩ :=
        (expectedReceipts_targets allowed ambient source.name source.key
          (equationTargetPhase orientation) target).mpr admitted
      exact ⟨⟨receipt, equationIndex, orientation⟩, receipt, member,
        by simp [targetEqual]⟩
  · simp [expectedEquationReceipts, active]

theorem equationBatch_targets_neighbors (allowed : List Token) (ambient : Nat)
    (source : State ambient) (target : Pattern) :
    (∃ receipt, (receipt, target) ∈
      (AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc source.pattern).answers) ↔
      ∃ next, target = (next : State ambient).pattern ∧ next ∈ neighbors allowed source := by
  rw [equationBatch_family]
  simp only [List.mem_append, exists_or]
  rw [expectedEquationTargets_spec, expectedEquationTargets_spec]
  rcases source with ⟨phase, index, token⟩
  cases phase <;> by_cases enabled : token ∈ allowed <;>
    simp [equationSourcePhase, equationTargetPhase, neighbors, opposite, enabled]

theorem equationBatch_targets_semantics (allowed : List Token) (ambient : Nat)
    (source : State ambient) (target : Pattern) :
    (∃ receipt, (receipt, target) ∈
      (AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc source.pattern).answers) ↔
      ∃ next, target = (next : State ambient).pattern ∧
        (EquationEdge allowed source next ∨ EquationEdge allowed next source) := by
  rw [equationBatch_targets_neighbors]
  simp only [neighbors_spec]

/-- Keep the position in the original provider snapshot before numbering the
successful query results. These two positions need not be equal. -/
def matchingProviderRows (allowed : List Token) (key : Token) : List (Token × Nat) :=
  allowed.zipIdx.filter fun row => row.1 == key

theorem matchingProviderRows_keys (allowed : List Token) (key : Token) :
    (matchingProviderRows allowed key).map Prod.fst =
      allowed.filter (fun token => token == key) := by
  simpa only [matchingProviderRows, Function.comp_def, List.zipIdx_map_fst] using
    (List.filter_map (f := Prod.fst) (p := fun token => token == key)
      (l := allowed.zipIdx)).symm

def ProviderPosition (allowed : List Token) (key : Token)
    (resultIndex providerRow : Nat) : Prop :=
  (matchingProviderRows allowed key)[resultIndex]? = some (key, providerRow)

theorem providerPosition_original (allowed : List Token) (key : Token)
    (resultIndex providerRow : Nat)
    (position : ProviderPosition allowed key resultIndex providerRow) :
    allowed[providerRow]? = some key := by
  have member := List.mem_of_getElem? position
  exact List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp member).1

theorem providerPosition_exists (allowed : List Token) (key : Token)
    (providerRow : Nat) (provided : allowed[providerRow]? = some key) :
    ∃ resultIndex, ProviderPosition allowed key resultIndex providerRow := by
  apply List.mem_iff_getElem?.mp
  exact List.mem_filter.mpr
    ⟨List.mk_mem_zipIdx_iff_getElem?.mpr provided, by simp⟩

theorem providerPosition_functional (allowed : List Token) (key : Token)
    (resultIndex leftRow rightRow : Nat)
    (left : ProviderPosition allowed key resultIndex leftRow)
    (right : ProviderPosition allowed key resultIndex rightRow) : leftRow = rightRow := by
  have equal := Option.some.inj (left.symm.trans right)
  exact congrArg Prod.snd equal

theorem expectedReceipts_provider_rows (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (phase : Phase) :
    expectedReceipts allowed ambient index token phase =
      (matchingProviderRows allowed token).zipIdx.map fun row =>
        expectedReceipt ambient index token phase row.2 := by
  unfold expectedReceipts
  rw [← matchingProviderRows_keys allowed token, List.zipIdx_map, List.map_map]
  rfl

theorem expectedReceipts_provider_spec (allowed : List Token) (ambient : Nat)
    (index : Fin (ambient + 1)) (token : Token) (phase : Phase) (receipt : Receipt) :
    receipt ∈ expectedReceipts allowed ambient index token phase ↔
      ∃ resultIndex providerRow, ProviderPosition allowed token resultIndex providerRow ∧
        receipt = expectedReceipt ambient index token phase resultIndex := by
  rw [expectedReceipts_provider_rows]
  constructor
  · intro member
    obtain ⟨⟨⟨rowKey, providerRow⟩, resultIndex⟩, row, equal⟩ := List.mem_map.mp member
    have selected := List.mk_mem_zipIdx_iff_getElem?.mp row
    have admitted := List.mem_filter.mp (List.mem_of_getElem? selected)
    have keyEq : rowKey = token := by simpa using admitted.2
    subst rowKey
    exact ⟨resultIndex, providerRow, selected, equal.symm⟩
  · rintro ⟨resultIndex, providerRow, position, rfl⟩
    exact List.mem_map.mpr
      ⟨((token, providerRow), resultIndex),
        List.mk_mem_zipIdx_iff_getElem?.mpr position, rfl⟩

def expectedRuleOrigin (ambient : Nat) (source : State ambient)
    (declaration : Fin 2) (resultIndex : Nat) : AuthoredEquationOccurrenceSearch.RuleOrigin :=
  ⟨expectedReceipt ambient source.name source.key .finished resultIndex, declaration.val⟩

theorem expectedRuleReceipts_spec (allowed : List Token) (ambient : Nat)
    (source : State ambient) (receipt : Receipt) :
    receipt ∈ expectedRuleReceipts allowed ambient source ↔
      source.phase = .exposed ∧
        ∃ resultIndex providerRow, ProviderPosition allowed source.key resultIndex providerRow ∧
          receipt = expectedReceipt ambient source.name source.key .finished resultIndex := by
  by_cases exposed : source.phase = .exposed
  · simp only [expectedRuleReceipts, exposed, if_true, true_and]
    exact expectedReceipts_provider_spec allowed ambient source.name source.key .finished receipt
  · simp [expectedRuleReceipts, exposed]

/-- Exact firing receipt coverage retains each authored declaration and its
successful query index, with a separate witness for the original provider row. -/
theorem firingBatch_answers_spec (allowed : List Token) (ambient : Nat)
    (source : State ambient) (origin : AuthoredEquationOccurrenceSearch.RuleOrigin)
    (target : Pattern) :
    (origin, target) ∈
      (AuthoredEquationOccurrenceSearch.firingBatch (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc source.pattern).answers ↔
      source.phase = .exposed ∧
        ∃ (declaration : Fin 2) (resultIndex providerRow : Nat),
          ProviderPosition allowed source.key resultIndex providerRow ∧
          origin = expectedRuleOrigin ambient source declaration resultIndex ∧
          target = (⟨.finished, source.name, source.key⟩ : State ambient).pattern := by
  rw [firingBatch_family]
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨receipt, member, equal⟩ | ⟨receipt, member, equal⟩)
    all_goals obtain ⟨exposed, resultIndex, providerRow, position, receiptEq⟩ :=
      (expectedRuleReceipts_spec allowed ambient source receipt).mp member
    · cases equal
      subst receipt
      exact ⟨exposed, 0, resultIndex, providerRow, position, rfl, rfl⟩
    · cases equal
      subst receipt
      exact ⟨exposed, 1, resultIndex, providerRow, position, rfl, rfl⟩
  · rintro ⟨exposed, declaration, resultIndex, providerRow, position, rfl, rfl⟩
    have member := (expectedRuleReceipts_spec allowed ambient source
      (expectedReceipt ambient source.name source.key .finished resultIndex)).mpr
        ⟨exposed, resultIndex, providerRow, position, rfl⟩
    have cases : declaration = 0 ∨ declaration = 1 := by omega
    rcases cases with rfl | rfl
    · exact Or.inl ⟨_, member, rfl⟩
    · exact Or.inr ⟨_, member, rfl⟩

theorem firingBatch_targets_semantics (allowed : List Token) (ambient : Nat)
    (source : State ambient) (target : Pattern) :
    (∃ receipt, (receipt, target) ∈
      (AuthoredEquationOccurrenceSearch.firingBatch (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc source.pattern).answers) ↔
      ∃ (origin : Origin) (next : State ambient),
        Firing allowed source origin next ∧ target = next.pattern := by
  constructor
  · rintro ⟨receipt, member⟩
    obtain ⟨exposed, declaration, resultIndex, providerRow, position, _, equal⟩ :=
      (firingBatch_answers_spec allowed ambient source receipt target).mp member
    rcases source with ⟨phase, name, key⟩
    cases exposed
    exact ⟨⟨declaration, providerRow⟩, ⟨.finished, name, key⟩,
      .consume name key declaration providerRow
        (providerPosition_original allowed key resultIndex providerRow position), equal⟩
  · rintro ⟨origin, next, firing, equal⟩
    cases firing with
    | consume name key declaration providerRow provided =>
      obtain ⟨resultIndex, position⟩ := providerPosition_exists allowed key providerRow provided
      exact ⟨expectedRuleOrigin ambient ⟨.exposed, name, key⟩ declaration resultIndex,
        (firingBatch_answers_spec allowed ambient _ _ target).mpr
          ⟨rfl, declaration, resultIndex, providerRow, position, rfl, equal⟩⟩

theorem actual_batches_complete (allowed : List Token) (ambient : Nat)
    (source : State ambient) :
    (AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc source.pattern).unresolved = [] ∧
    (AuthoredEquationOccurrenceSearch.firingBatch (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc source.pattern).unresolved = [] := by
  rw [equationBatch_family, firingBatch_family]
  exact ⟨rfl, rfl⟩

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfile
