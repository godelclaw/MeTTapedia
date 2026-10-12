import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileComparisons
import Mettapedia.OSLF.MeTTaIL.EquationOccurrenceNativeReceipts
import Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated

/-!
# Certified actual runtime frontiers for the guarded binder family

The finite family has at most two equation presentations per name and key.
The source and its actual conditional-equation discoveries therefore supply
a complete certificate. Primitive readouts are executed at those actual
presentations, retaining full equation and rule receipts, successful-query
ordinals, and separately recovered original provider rows. Coverage is proved
against the independently specified equation and firing judgments.

Different equation histories can justify the same primitive occurrence. The
primitive readout below identifies an occurrence by its representative,
authored declaration, original provider row and target; equation histories
are retained as justification and do not increase its physical event count.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderCertifiedRuntime

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Engine
open Mettapedia.GSLT.LanguageDef.WellSorted
open EquationFrontierBinderProfile
open Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier

open Mettapedia.OSLF.Framework

abbrev RuntimeEntry := Entry Pattern ConditionalEquationExecution.EquationReceipt
abbrev RuntimeReceipt := EquationOccurrenceNativeReceipts.RuntimeReceipt

def root {ambient : Nat} (source : State ambient) : RuntimeEntry :=
  ⟨source.pattern, []⟩

def actualModel (ambient : Nat) (allowed : List Token) :=
  AuthoredEquationOccurrenceSearch.model (provider allowed) language FreeTypeContext.empty (ambientContext ambient) .proc

def entries {ambient : Nat} (allowed : List Token) (source : State ambient) :
    List RuntimeEntry :=
  root source :: discoveries (root source) ((actualModel ambient allowed).equations source.pattern).answers

/-- Each equation discovery keeps its actual authored receipt, including the
query history; repeated successful equation rows remain separate histories. -/
def coverageCertificate {ambient : Nat} (allowed : List Token) (source : State ambient) :
    FiniteEquationCoverage.Certificate Pattern where
  walks := ((actualModel ambient allowed).equations source.pattern).answers.map
    fun answer => [answer.2]

/-- Actual primitive firings are executed at every retained presentation.
Their list indices and complete typed conditional receipts remain available. -/
def execute {ambient : Nat} (allowed : List Token) (source : State ambient) :
    List RuntimeReceipt :=
  (entries allowed source).flatMap fun entry =>
    readouts entry ((actualModel ambient allowed).firings entry.state).answers

theorem equivalent_direct {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    Relation.EqvGen (EquationEdge allowed) source target ↔
      target = source ∨ target ∈ neighbors allowed source := by
  rw [← representatives_complete allowed source target]
  simp [EquationFrontierBinderProfile.certificate, FiniteEquationCoverage.Certificate.representatives,
    FiniteEquationCoverage.walkEnd]

theorem certificate_representatives_spec {ambient : Nat} (allowed : List Token)
    (source : State ambient) (raw : Pattern) :
    raw ∈ (coverageCertificate allowed source).representatives source.pattern ↔
      ∃ target : State ambient, raw = target.pattern ∧
        Relation.EqvGen (EquationEdge allowed) source target := by
  simp only [coverageCertificate, FiniteEquationCoverage.Certificate.representatives, List.map_map,
    List.mem_cons, List.mem_map, Function.comp_def, FiniteEquationCoverage.walkEnd]
  constructor
  · rintro (same | ⟨answer, member, equal⟩)
    · exact ⟨source, same, .refl source⟩
    · have actual : ∃ receipt, (receipt, raw) ∈
        (AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language FreeTypeContext.empty
          (ambientContext ambient) .proc source.pattern).answers := by
        exact ⟨answer.1, equal ▸ member⟩
      obtain ⟨target, targetEq, neighbor⟩ :=
        (equationBatch_targets_neighbors allowed ambient source raw).mp actual
      exact ⟨target, targetEq, (equivalent_direct allowed source target).mpr
        (Or.inr neighbor)⟩
  · rintro ⟨target, targetEq, equivalent⟩
    rcases (equivalent_direct allowed source target).mp equivalent with same | neighbor
    · exact Or.inl (targetEq.trans (congrArg State.pattern same))
    · obtain ⟨receipt, member⟩ :=
        (equationBatch_targets_neighbors allowed ambient source raw).mpr
          ⟨target, targetEq, neighbor⟩
      exact Or.inr ⟨(receipt, raw), member, rfl⟩

theorem entries_states {ambient : Nat} (allowed : List Token) (source : State ambient) :
    (entries allowed source).map Entry.state =
      (coverageCertificate allowed source).representatives source.pattern := by
  simp [entries, root, discoveries, Entry.extend, coverageCertificate,
    FiniteEquationCoverage.Certificate.representatives, FiniteEquationCoverage.walkEnd]

theorem entries_represent_state {ambient : Nat} (allowed : List Token)
    (source : State ambient) (entry : RuntimeEntry) (member : entry ∈ entries allowed source) :
    ∃ target : State ambient, entry.state = target.pattern ∧
      Relation.EqvGen (EquationEdge allowed) source target := by
  apply (certificate_representatives_spec allowed source entry.state).mp
  rw [← entries_states]
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

theorem entries_cover {ambient : Nat} (allowed : List Token)
    (source target : State ambient)
    (equivalent : Relation.EqvGen (EquationEdge allowed) source target) :
    ∃ entry ∈ entries allowed source, entry.state = target.pattern := by
  apply List.mem_map.mp
  rw [entries_states]
  exact (certificate_representatives_spec allowed source target.pattern).mpr
    ⟨target, rfl, equivalent⟩

/-- The real equation provider checks the certificate's walks and closure.
This is an earned executable certificate, rather than a completeness field. -/
theorem certificate_checked {ambient : Nat} (allowed : List Token) (source : State ambient) :
    (coverageCertificate allowed source).check
      (ResumableEquationCoverage.equationNeighbors (actualModel ambient allowed)) source.pattern = true := by
  apply (FiniteEquationCoverage.check_spec _ _ _).mpr
  constructor
  · intro walk member
    obtain ⟨answer, answerMember, rfl⟩ := List.mem_map.mp member
    have neighbor : answer.2 ∈ ResumableEquationCoverage.equationNeighbors (actualModel ambient allowed)
        source.pattern := List.mem_map.mpr ⟨answer, answerMember, rfl⟩
    simp [FiniteEquationCoverage.checkWalk, neighbor]
  · intro raw represented next neighbor
    obtain ⟨state, rawEq, before⟩ :=
      (certificate_representatives_spec allowed source raw).mp represented
    subst raw
    obtain ⟨answer, actual, targetEq⟩ := List.mem_map.mp neighbor
    have actualTarget : ∃ receipt, (receipt, next) ∈
        (AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language FreeTypeContext.empty
          (ambientContext ambient) .proc state.pattern).answers :=
      ⟨answer.1, targetEq ▸ actual⟩
    obtain ⟨target, nextEq, edge⟩ :=
      (equationBatch_targets_semantics allowed ambient state next).mp actualTarget
    have after : Relation.EqvGen (EquationEdge allowed) state target := by
      rcases edge with forward | reverse
      · exact .rel _ _ forward
      · exact .symm _ _ (.rel _ _ reverse)
    exact (certificate_representatives_spec allowed source next).mpr
      ⟨target, nextEq, .trans _ _ _ before after⟩

theorem entries_valid {ambient : Nat} (allowed : List Token) (source : State ambient)
    (entry : RuntimeEntry) (member : entry ∈ entries allowed source) :
    entry.Valid (AuthoredEquationOccurrenceSemantics.Equation (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc) source.pattern := by
  simp only [entries, List.mem_cons] at member
  rcases member with same | discovered
  · subst entry
    rfl
  · obtain ⟨answer, actual, same⟩ := List.mem_map.mp discovered
    cases same
    apply Entry.valid_extend
    · rfl
    · exact AuthoredEquationOccurrenceSemantics.equations_sound (provider allowed) language FreeTypeContext.empty
        (ambientContext ambient) .proc source.pattern answer.2 answer.1 actual

theorem execute_readout_spec {ambient : Nat} (allowed : List Token) (source : State ambient)
    (receipt : RuntimeReceipt) :
    receipt ∈ execute allowed source ↔
      ∃ entry ∈ entries allowed source,
        ∃ answerIndex ∈ ((actualModel ambient allowed).firings entry.state).answers.zipIdx,
          (⟨entry, answerIndex.2, answerIndex.1.1, answerIndex.1.2⟩ : RuntimeReceipt) = receipt := by
  simp [execute, List.mem_flatMap, readouts, List.mem_map]

theorem execute_sound {ambient : Nat} (allowed : List Token) (source : State ambient)
    (receipt : RuntimeReceipt) (member : receipt ∈ execute allowed source) :
    receipt.Valid (AuthoredEquationOccurrenceSemantics.Equation (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc)
      (AuthoredEquationOccurrenceSemantics.Firing (provider allowed) language FreeTypeContext.empty
        (ambientContext ambient) .proc) source.pattern := by
  obtain ⟨entry, entryMember, ⟨⟨origin, target⟩, ordinal⟩, selected, rfl⟩ :=
    (execute_readout_spec allowed source receipt).mp member
  exact ⟨entries_valid allowed source entry entryMember,
    AuthoredEquationOccurrenceSemantics.firings_sound (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc entry.state target origin
        (List.fst_mem_of_mem_zipIdx selected)⟩

/-- A returned primitive receipt has an independent firing with the original
provider row. Its successful-result ordinal is retained as a separate value. -/
theorem execute_original_occurrence_sound {ambient : Nat} (allowed : List Token)
    (source : State ambient) (receipt : RuntimeReceipt) (member : receipt ∈ execute allowed source) :
    ∃ (representative next : State ambient) (declaration : Fin 2)
        (resultIndex providerRow : Nat),
      Relation.EqvGen (EquationEdge allowed) source representative ∧
      Firing allowed representative ⟨declaration, providerRow⟩ next ∧
      receipt.representative.state = representative.pattern ∧
      receipt.origin = expectedRuleOrigin ambient representative declaration resultIndex ∧
      ProviderPosition allowed representative.key resultIndex providerRow ∧
      receipt.target = next.pattern := by
  obtain ⟨entry, entryMember, ⟨⟨origin, target⟩, ordinal⟩, selected, rfl⟩ :=
    (execute_readout_spec allowed source receipt).mp member
  obtain ⟨representative, stateEq, before⟩ := entries_represent_state allowed source entry entryMember
  have actual := List.fst_mem_of_mem_zipIdx selected
  rw [stateEq] at actual
  obtain ⟨exposed, declaration, resultIndex, providerRow, position, originEq, targetEq⟩ :=
    (firingBatch_answers_spec allowed ambient representative origin target).mp actual
  refine ⟨representative, ⟨.finished, representative.name, representative.key⟩,
    declaration, resultIndex, providerRow, before, ?_, stateEq, originEq, position, targetEq⟩
  rcases representative with ⟨phase, name, key⟩
  cases exposed
  exact .consume name key declaration providerRow
    (providerPosition_original allowed key resultIndex providerRow position)

/-- Every independently admitted authored firing and original provider row
is represented by a whole actual runtime receipt, including its readout index. -/
theorem execute_original_occurrence_complete {ambient : Nat} (allowed : List Token)
    (source representative next : State ambient) (origin : Origin)
    (before : Relation.EqvGen (EquationEdge allowed) source representative)
    (firing : Firing allowed representative origin next) :
    ∃ receipt ∈ execute allowed source,
      receipt.representative.state = representative.pattern ∧
      ∃ resultIndex, ProviderPosition allowed representative.key resultIndex origin.providerRow ∧
        receipt.origin = expectedRuleOrigin ambient representative origin.declaration resultIndex ∧
        receipt.target = next.pattern := by
  obtain ⟨entry, entryMember, stateEq⟩ := entries_cover allowed source representative before
  cases firing with
  | consume name key declaration providerRow provided =>
    obtain ⟨resultIndex, position⟩ := providerPosition_exists allowed key providerRow provided
    let ruleOrigin := expectedRuleOrigin ambient
      (⟨.exposed, name, key⟩ : State ambient) declaration resultIndex
    have answer : (ruleOrigin, (⟨.finished, name, key⟩ : State ambient).pattern) ∈
        ((actualModel ambient allowed).firings entry.state).answers := by
      rw [stateEq]
      exact (firingBatch_answers_spec allowed ambient _ _ _).mpr
        ⟨rfl, declaration, resultIndex, providerRow, position, rfl, rfl⟩
    obtain ⟨ordinal, selected⟩ := ResumableEquationCoverage.exists_answer_ordinal _ _ answer
    refine ⟨⟨entry, ordinal, ruleOrigin, (⟨.finished, name, key⟩ : State ambient).pattern⟩,
      ?_, stateEq, resultIndex, position, rfl, rfl⟩
    exact (execute_readout_spec allowed source _).mpr
      ⟨entry, entryMember, ((ruleOrigin, _), ordinal), selected, rfl⟩

structure PrimitiveOccurrence (ambient : Nat) where
  representative : State ambient
  origin : Origin
  target : State ambient
  deriving DecidableEq, Repr

/-- Primitive identity forgets the equation justification and the position in
the returned receipt list. It retains the actual authored declaration and
the original provider-row occurrence, including repeated equal provider rows. -/
def PrimitiveReadout {ambient : Nat} (allowed : List Token) (receipt : RuntimeReceipt)
    (event : PrimitiveOccurrence ambient) : Prop :=
  receipt.representative.state = event.representative.pattern ∧
    ∃ resultIndex, ProviderPosition allowed event.representative.key resultIndex
      event.origin.providerRow ∧
      receipt.origin = expectedRuleOrigin ambient event.representative
        event.origin.declaration resultIndex ∧ receipt.target = event.target.pattern

theorem primitiveReadout_unique {ambient : Nat} (allowed : List Token)
    (receipt : RuntimeReceipt) (left right : PrimitiveOccurrence ambient)
    (leftReadout : PrimitiveReadout allowed receipt left)
    (rightReadout : PrimitiveReadout allowed receipt right) : left = right := by
  rcases left with ⟨leftState, ⟨leftDeclaration, leftRow⟩, leftTarget⟩
  rcases right with ⟨rightState, ⟨rightDeclaration, rightRow⟩, rightTarget⟩
  obtain ⟨leftStateEq, leftResult, leftPosition, leftOriginEq, leftTargetEq⟩ := leftReadout
  obtain ⟨rightStateEq, rightResult, rightPosition, rightOriginEq, rightTargetEq⟩ := rightReadout
  dsimp only at leftStateEq rightStateEq leftPosition rightPosition leftOriginEq rightOriginEq leftTargetEq rightTargetEq
  have stateEq := state_pattern_injective (leftStateEq.symm.trans rightStateEq)
  have targetEq := state_pattern_injective (leftTargetEq.symm.trans rightTargetEq)
  subst rightState
  subst rightTarget
  have originEq := leftOriginEq.symm.trans rightOriginEq
  have declarationEq : leftDeclaration = rightDeclaration :=
    Fin.ext (congrArg AuthoredEquationOccurrenceSearch.RuleOrigin.ruleIndex originEq)
  have historyEq := congrArg
    (fun origin : AuthoredEquationOccurrenceSearch.RuleOrigin => origin.history) originEq
  have resultEq : leftResult = rightResult := by
    simpa [expectedRuleOrigin, EquationFrontierBinderProfile.expectedReceipt] using historyEq
  subst rightResult
  have rowEq := providerPosition_functional allowed leftState.key leftResult
    leftRow rightRow leftPosition rightPosition
  simp [declarationEq, rowEq]

theorem execute_unique_primitive_readout {ambient : Nat} (allowed : List Token)
    (source : State ambient) (receipt : RuntimeReceipt) (member : receipt ∈ execute allowed source) :
    ∃! event : PrimitiveOccurrence ambient, PrimitiveReadout allowed receipt event := by
  obtain ⟨representative, next, declaration, resultIndex, providerRow,
    _, _, representativeEq, originEq, position, targetEq⟩ :=
      execute_original_occurrence_sound allowed source receipt member
  let actual : PrimitiveOccurrence ambient := ⟨representative, ⟨declaration, providerRow⟩, next⟩
  have readout : PrimitiveReadout allowed receipt actual :=
    ⟨representativeEq, resultIndex, position, originEq, targetEq⟩
  exact ⟨actual, readout, fun event represented =>
    primitiveReadout_unique allowed receipt event actual represented readout⟩

/-- Equation receipts are justifications of an occurrence, not extra primitive
events. Forgetting those histories gives exactly the independent occurrence
frontier, while all original provider and authored declaration positions remain. -/
theorem primitive_occurrence_coverage {ambient : Nat} (allowed : List Token)
    (source : State ambient) (event : PrimitiveOccurrence ambient) :
    (∃ receipt ∈ execute allowed source, PrimitiveReadout allowed receipt event) ↔
      Relation.EqvGen (EquationEdge allowed) source event.representative ∧
        Firing allowed event.representative event.origin event.target := by
  constructor
  · rintro ⟨receipt, member, readout⟩
    obtain ⟨representative, next, declaration, resultIndex, providerRow,
      before, firing, representativeEq, originEq, position, targetEq⟩ :=
        execute_original_occurrence_sound allowed source receipt member
    let actual : PrimitiveOccurrence ambient := ⟨representative, ⟨declaration, providerRow⟩, next⟩
    have actualReadout : PrimitiveReadout allowed receipt actual :=
      ⟨representativeEq, resultIndex, position, originEq, targetEq⟩
    have equal := primitiveReadout_unique allowed receipt actual event actualReadout readout
    rw [← equal]
    exact ⟨before, firing⟩
  · rintro ⟨before, firing⟩
    obtain ⟨receipt, member, stateEq, resultIndex, position, originEq, targetEq⟩ :=
      execute_original_occurrence_complete allowed source event.representative event.target
        event.origin before firing
    exact ⟨receipt, member, stateEq, resultIndex, position, originEq, targetEq⟩

/-- Full actual receipts cover exactly the independently generated successor
classes, including equation detours before and after the primitive firing. -/
theorem execute_endpoint_coverage {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    (∃ receipt ∈ execute allowed source, ∃ next : State ambient,
      receipt.target = next.pattern ∧ Relation.EqvGen (EquationEdge allowed) next target) ↔
        EquationFrontierBinderProfile.Step allowed source target := by
  constructor
  · rintro ⟨receipt, member, next, targetEq, after⟩
    obtain ⟨representative, actualNext, declaration, resultIndex, providerRow,
      before, firing, _, _, _, actualTargetEq⟩ :=
        execute_original_occurrence_sound allowed source receipt member
    have same := state_pattern_injective (actualTargetEq.symm.trans targetEq)
    subst actualNext
    exact ⟨representative, ⟨⟨declaration, providerRow⟩, next⟩, before, firing, after⟩
  · rintro ⟨representative, ⟨origin, next⟩, before, firing, after⟩
    obtain ⟨receipt, member, _, resultIndex, _, _, targetEq⟩ :=
      execute_original_occurrence_complete allowed source representative next origin before firing
    exact ⟨receipt, member, next, targetEq, after⟩

def targets {ambient : Nat} (allowed : List Token) (source : State ambient) : List Pattern :=
  (execute allowed source).map Receipt.target

/-- Tests may observe actual raw endpoints. Their only semantic requirement
is invariance under the independently generated equation classes. -/
theorem execute_diamond {ambient : Nat} (allowed : List Token) (source : State ambient)
    (test : Pattern → Bool)
    (invariant : ∀ before after : State ambient,
      Relation.EqvGen (EquationEdge allowed) before after →
        test before.pattern = test after.pattern) :
    (targets allowed source).any test = true ↔
      ∃ target : State ambient, EquationFrontierBinderProfile.Step allowed source target ∧
        test target.pattern = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨raw, present, succeeds⟩
    obtain ⟨receipt, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨representative, next, declaration, resultIndex, providerRow,
      before, firing, _, _, _, targetEq⟩ :=
        execute_original_occurrence_sound allowed source receipt member
    exact ⟨next, ⟨representative, ⟨⟨declaration, providerRow⟩, next⟩,
      before, firing, .refl next⟩, targetEq ▸ succeeds⟩
  · rintro ⟨target, step, succeeds⟩
    obtain ⟨receipt, member, next, targetEq, after⟩ :=
      (execute_endpoint_coverage allowed source target).mpr step
    exact ⟨receipt.target, List.mem_map.mpr ⟨receipt, member, rfl⟩,
      targetEq.symm ▸ (invariant next target after).trans succeeds⟩

/-- This executable universal modality quantifies over outgoing successors. -/
theorem execute_outgoing_universal {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : Pattern → Bool)
    (invariant : ∀ before after : State ambient,
      Relation.EqvGen (EquationEdge allowed) before after →
        test before.pattern = test after.pattern) :
    (targets allowed source).all test = true ↔
      ∀ target : State ambient, EquationFrontierBinderProfile.Step allowed source target →
        test target.pattern = true := by
  rw [List.all_eq_true]
  constructor
  · intro universal target step
    obtain ⟨receipt, member, next, targetEq, after⟩ :=
      (execute_endpoint_coverage allowed source target).mpr step
    exact (invariant next target after).symm.trans
      (targetEq ▸ universal receipt.target (List.mem_map.mpr ⟨receipt, member, rfl⟩))
  · intro universal raw present
    obtain ⟨receipt, member, rfl⟩ := List.mem_map.mp present
    obtain ⟨representative, next, declaration, resultIndex, providerRow,
      before, firing, _, _, _, targetEq⟩ :=
        execute_original_occurrence_sound allowed source receipt member
    exact targetEq.symm ▸ universal next
      ⟨representative, ⟨⟨declaration, providerRow⟩, next⟩, before, firing, .refl next⟩

theorem execute_empty_iff {ambient : Nat} (allowed : List Token) (source : State ambient) :
    execute allowed source = [] ↔
      ¬ ∃ target : State ambient, EquationFrontierBinderProfile.Step allowed source target := by
  constructor
  · intro empty ⟨target, step⟩
    obtain ⟨receipt, member, _⟩ := (execute_endpoint_coverage allowed source target).mpr step
    simp [empty] at member
  · intro absent
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro receipt member
    obtain ⟨representative, next, declaration, resultIndex, providerRow,
      before, firing, _, _, _, _⟩ :=
        execute_original_occurrence_sound allowed source receipt member
    exact absent ⟨next, representative, ⟨⟨declaration, providerRow⟩, next⟩,
      before, firing, .refl next⟩

/-- Each actual receipt enters the existing dependent native family, retaining
its conversion trace, authored origin and genuinely typed target evidence. -/
def nativeReceipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (receipt : RuntimeReceipt) (member : receipt ∈ execute allowed source) :
    EquationOccurrenceNativeReceipts.ReceiptFamily (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc source.pattern :=
  ⟨receipt, execute_sound allowed source receipt member⟩

def sortedNativeReceipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (receipt : RuntimeReceipt) (member : receipt ∈ execute allowed source) :=
  EquationOccurrenceNativeReceipts.sortedNative (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc
    (nativeReceipt allowed source receipt member)

theorem native_one_primitive_event {ambient : Nat} (allowed : List Token)
    (source : State ambient) (receipt : RuntimeReceipt) (member : receipt ∈ execute allowed source) :
    (EquationOccurrenceNativeReceipts.history (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc
      (nativeReceipt allowed source receipt member)).length = 1 :=
  EquationOccurrenceNativeReceipts.history_primitive_count (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc _

/-- The actual conditional runtime frontier is complete for the genuine raw
generated GSLT on the admitted canonical carrier. -/
theorem generated_endpoint_coverage {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    (∃ receipt ∈ execute allowed source, ∃ next : State ambient,
      receipt.target = next.pattern ∧ Relation.EqvGen (EquationEdge allowed) next target) ↔
        Mettapedia.GSLT.LanguageDef.EquationSemantics.StepModuloEquations
          (EquationFrontierBinderProfileGenerated.base allowed) language
          source.pattern target.pattern := by
  rw [EquationFrontierBinderProfileGenerated.generated_gslt_step_comparison]
  exact execute_endpoint_coverage allowed source target

theorem generated_diamond {ambient : Nat} (allowed : List Token) (source : State ambient)
    (test : Pattern → Bool)
    (invariant : ∀ before after : State ambient,
      Relation.EqvGen (EquationEdge allowed) before after →
        test before.pattern = test after.pattern) :
    (targets allowed source).any test = true ↔
      ∃ target : State ambient,
        Mettapedia.GSLT.LanguageDef.EquationSemantics.StepModuloEquations
          (EquationFrontierBinderProfileGenerated.base allowed) language
          source.pattern target.pattern ∧ test target.pattern = true := by
  simp only [EquationFrontierBinderProfileGenerated.generated_gslt_step_comparison]
  exact execute_diamond allowed source test invariant

theorem generated_outgoing_universal {ambient : Nat} (allowed : List Token)
    (source : State ambient) (test : Pattern → Bool)
    (invariant : ∀ before after : State ambient,
      Relation.EqvGen (EquationEdge allowed) before after →
        test before.pattern = test after.pattern) :
    (targets allowed source).all test = true ↔
      ∀ target : State ambient,
        Mettapedia.GSLT.LanguageDef.EquationSemantics.StepModuloEquations
          (EquationFrontierBinderProfileGenerated.base allowed) language
          source.pattern target.pattern → test target.pattern = true := by
  simp only [EquationFrontierBinderProfileGenerated.generated_gslt_step_comparison]
  exact execute_outgoing_universal allowed source test invariant

/-- A completed empty actual frontier excludes even noncanonical raw targets;
the existing alpha normalization theorem covers their canonical carrier. -/
theorem generated_empty_iff {ambient : Nat} (allowed : List Token) (source : State ambient) :
    execute allowed source = [] ↔
      ¬ ∃ rawTarget : Pattern,
        Mettapedia.GSLT.LanguageDef.EquationSemantics.StepModuloEquations
          (EquationFrontierBinderProfileGenerated.base allowed) language
          source.pattern rawTarget := by
  rw [execute_empty_iff]
  constructor
  · intro noFinite ⟨rawTarget, rawStep⟩
    obtain ⟨target, _, finite⟩ :=
      EquationFrontierBinderProfileGenerated.raw_modulo_class_normalization
        allowed source rawTarget rawStep
    exact noFinite ⟨target, finite⟩
  · intro noRaw ⟨target, finite⟩
    exact noRaw ⟨target.pattern,
      (EquationFrontierBinderProfileGenerated.generated_gslt_step_comparison
        allowed source target).mpr finite⟩

theorem execute_match_origin {ambient : Nat} (allowed : List Token) (source : State ambient)
    (receipt : RuntimeReceipt) (member : receipt ∈ execute allowed source) :
    receipt.origin.matchIndex = 0 := by
  obtain ⟨representative, next, declaration, resultIndex, providerRow,
    _, _, _, originEq, _, _⟩ := execute_original_occurrence_sound allowed source receipt member
  rw [originEq]
  rfl

theorem tucked_actual_firing {ambient : Nat} (name : Fin (ambient + 1)) :
    ∃ receipt ∈ execute [.permit] (⟨.tucked, name, .permit⟩ : State ambient),
      receipt.target = (⟨.finished, name, .permit⟩ : State ambient).pattern := by
  obtain ⟨receipt, member, _, resultIndex, _, _, targetEq⟩ :=
    execute_original_occurrence_complete [.permit] ⟨.tucked, name, .permit⟩
      ⟨.exposed, name, .permit⟩ ⟨.finished, name, .permit⟩ ⟨0, 0⟩
      (.rel _ _ (.extrusion name .permit (by simp)))
      (.consume name .permit 0 0 rfl)
  exact ⟨receipt, member, targetEq⟩

theorem refused_actual_frontier_empty {ambient : Nat} (name : Fin (ambient + 1)) :
    execute [.permit] (⟨.tucked, name, .revoked⟩ : State ambient) = [] :=
  (execute_empty_iff [.permit] ⟨.tucked, name, .revoked⟩).mpr
    (failed_query_has_no_step name)

/-- Skipped rows and repeated admitted rows have distinct original positions;
successful-result numbering alone would erase this information. -/
theorem sparse_duplicate_provider_positions :
    ProviderPosition [.revoked, .permit, .reserve, .permit] .permit 0 1 ∧
      ProviderPosition [.revoked, .permit, .reserve, .permit] .permit 1 3 := by
  unfold ProviderPosition
  decide +kernel

theorem sparse_duplicate_actual_occurrences {ambient : Nat} (name : Fin (ambient + 1))
    (declaration : Fin 2) :
    (∃ receipt ∈ execute [.revoked, .permit, .reserve, .permit]
        (⟨.tucked, name, .permit⟩ : State ambient),
      PrimitiveReadout [.revoked, .permit, .reserve, .permit] receipt
        ⟨⟨.exposed, name, .permit⟩, ⟨declaration, 1⟩, ⟨.finished, name, .permit⟩⟩) ∧
    (∃ receipt ∈ execute [.revoked, .permit, .reserve, .permit]
        (⟨.tucked, name, .permit⟩ : State ambient),
      PrimitiveReadout [.revoked, .permit, .reserve, .permit] receipt
        ⟨⟨.exposed, name, .permit⟩, ⟨declaration, 3⟩, ⟨.finished, name, .permit⟩⟩) := by
  constructor
  · apply (primitive_occurrence_coverage _ _ _).mpr
    exact ⟨.rel _ _ (.extrusion name .permit (by simp)),
      .consume name .permit declaration 1 rfl⟩
  · apply (primitive_occurrence_coverage _ _ _).mpr
    exact ⟨.rel _ _ (.extrusion name .permit (by simp)),
      .consume name .permit declaration 3 rfl⟩

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderCertifiedRuntime
