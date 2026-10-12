import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderProfileComparisons
import Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderSearch
import Mettapedia.OSLF.Framework.EquationFrontierBinderProfileGenerated

/-!
# Semantic coverage of the actual resumable binder search

An executable carrier decoder admits canonical binder-family states. Admitted
states run the unchanged authored conditional-equation and rule interpreters;
undecoded states retain a carrier obligation. The queue's semantic comparisons
use independent equation generators and actual scoped rule-instance judgments.
Complete endpoint and modal readouts are earned from quiescence and the proved
local interpreter contracts. Primitive origins retain the original receipts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderCertifiedSearch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax Engine
open EquationFrontierBinderProfile
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.ResumableEquationOccurrenceFrontier


def decode (ambient : Nat) (source : Pattern) : Option (State ambient) :=
  (allStates ambient).find? fun state => state.pattern == source

theorem decode_sound (ambient : Nat) (source : Pattern) (state : State ambient)
    (found : decode ambient source = some state) : state.pattern = source := by
  have selected := List.find?_some (p := fun candidate : State ambient => candidate.pattern == source) found
  exact beq_iff_eq.mp selected

theorem decode_state {ambient : Nat} (state : State ambient) :
    decode ambient state.pattern = some state := by
  cases found : decode ambient state.pattern with
  | none =>
    have omitted := List.find?_eq_none.mp found
    have rejected := omitted state (allStates_complete state)
    simp at rejected
  | some selected =>
    have equal := state_pattern_injective (decode_sound ambient state.pattern selected found)
    subst selected
    rfl

theorem decode_spec (ambient : Nat) (source : Pattern) (state : State ambient) :
    decode ambient source = some state ↔ state.pattern = source := by
  constructor
  · exact decode_sound ambient source state
  · rintro rfl
    exact decode_state state

inductive Obligation where
  | outsideCarrier (source : Pattern)
  | authored (reason : AuthoredEquationOccurrenceSearch.Obligation)
  deriving DecidableEq, Repr

def equationBatch (ambient : Nat) (allowed : List Token) (source : Pattern) :
    Batch (ConditionalEquationExecution.EquationReceipt × Pattern) Obligation :=
  match decode ambient source with
  | none => ⟨[], [.outsideCarrier source]⟩
  | some _ =>
    let actual := AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc source
    ⟨actual.answers, actual.unresolved.map Obligation.authored⟩

def firingBatch (ambient : Nat) (allowed : List Token) (source : Pattern) :
    Batch (AuthoredEquationOccurrenceSearch.RuleOrigin × Pattern) Obligation :=
  match decode ambient source with
  | none => ⟨[], [.outsideCarrier source]⟩
  | some _ =>
    let actual := AuthoredEquationOccurrenceSearch.firingBatch (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc source
    ⟨actual.answers, actual.unresolved.map Obligation.authored⟩

def model (ambient : Nat) (allowed : List Token) :
    Model Pattern ConditionalEquationExecution.EquationReceipt AuthoredEquationOccurrenceSearch.RuleOrigin Obligation where
  equations := equationBatch ambient allowed
  firings := firingBatch ambient allowed

def execute {ambient : Nat} (allowed : List Token) (fuel : Nat) (source : State ambient) :=
  run (model ambient allowed) fuel (initial source.pattern)

theorem equationBatch_state {ambient : Nat} (allowed : List Token) (source : State ambient) :
    equationBatch ambient allowed source.pattern =
      ⟨(AuthoredEquationOccurrenceSearch.equationBatch (provider allowed) language FreeTypeContext.empty
        (ambientContext ambient) .proc source.pattern).answers, []⟩ := by
  rw [equationBatch, decode_state]
  simp only [(actual_batches_complete allowed ambient source).1, List.map_nil]

theorem firingBatch_state {ambient : Nat} (allowed : List Token) (source : State ambient) :
    firingBatch ambient allowed source.pattern =
      ⟨(AuthoredEquationOccurrenceSearch.firingBatch (provider allowed) language FreeTypeContext.empty
        (ambientContext ambient) .proc source.pattern).answers, []⟩ := by
  rw [firingBatch, decode_state]
  simp only [(actual_batches_complete allowed ambient source).2, List.map_nil]

/-- Equation admission refers to the independently defined authored extrusion
generator on the finite typed carrier, not the provider's answer membership. -/
def Equation (ambient : Nat) (allowed : List Token) (source target : Pattern) : Prop :=
  ∃ before after : State ambient,
    source = before.pattern ∧ target = after.pattern ∧ EquationEdge allowed before after

/-- A primitive occurrence is an actual scoped rule instance at an admitted
source. Its complete CE receipt and authored declaration index remain visible. -/
def Firing (ambient : Nat) (allowed : List Token) (source : Pattern)
    (origin : AuthoredEquationOccurrenceSearch.RuleOrigin) (target : Pattern) : Prop :=
  ∃ state : State ambient, source = state.pattern ∧
    AuthoredEquationOccurrenceSemantics.Firing (provider allowed) language FreeTypeContext.empty (ambientContext ambient)
      .proc source origin target

theorem rules_supported : AuthoredEquationOccurrenceSemantics.RulesSupported language := by
  intro rule authored spec declared
  simp only [language, List.mem_cons, List.not_mem_nil, or_false] at authored
  rcases authored with rfl | rfl
  all_goals simp only [consumeRule, Option.some.injEq] at declared
  all_goals subst spec
  all_goals decide +kernel

theorem equations_sound (ambient : Nat) (allowed : List Token) (source target : Pattern)
    (present : target ∈ ResumableEquationCoverage.equationNeighbors (model ambient allowed) source) :
    Equation ambient allowed source target ∨ Equation ambient allowed target source := by
  cases decoded : decode ambient source with
  | none => simp [ResumableEquationCoverage.equationNeighbors, model, equationBatch, decoded] at present
  | some state =>
    have equal := decode_sound ambient source state decoded
    subst source
    simp only [ResumableEquationCoverage.equationNeighbors, model, equationBatch_state] at present
    obtain ⟨⟨origin, next⟩, member, targetEq⟩ := List.mem_map.mp present
    simp only at targetEq
    subst next
    obtain ⟨next, nextEq, edge⟩ :=
      (equationBatch_targets_semantics allowed ambient state target).mp ⟨origin, member⟩
    rcases edge with forward | reverse
    · exact Or.inl ⟨state, next, rfl, nextEq, forward⟩
    · exact Or.inr ⟨next, state, nextEq, rfl, reverse⟩

theorem equation_neighbor_complete {ambient : Nat} (allowed : List Token)
    (source target : State ambient)
    (edge : EquationEdge allowed source target ∨ EquationEdge allowed target source) :
    target.pattern ∈ ResumableEquationCoverage.equationNeighbors (model ambient allowed) source.pattern := by
  obtain ⟨origin, actual⟩ :=
    (equationBatch_targets_semantics allowed ambient source target.pattern).mpr ⟨target, rfl, edge⟩
  simp only [ResumableEquationCoverage.equationNeighbors, model, equationBatch_state]
  exact List.mem_map.mpr ⟨(origin, target.pattern), actual, rfl⟩

theorem equations_complete (ambient : Nat) (allowed : List Token) (source : Pattern)
    (_complete : ((model ambient allowed).equations source).unresolved = [])
    (target : Pattern)
    (edge : Equation ambient allowed source target ∨ Equation ambient allowed target source) :
    target ∈ ResumableEquationCoverage.equationNeighbors (model ambient allowed) source := by
  rcases edge with ⟨before, after, rfl, rfl, forward⟩ | ⟨before, after, rfl, rfl, reverse⟩
  · exact equation_neighbor_complete allowed before after (Or.inl forward)
  · exact equation_neighbor_complete allowed after before (Or.inr reverse)

theorem firings_sound (ambient : Nat) (allowed : List Token) (source : Pattern)
    (answer : AuthoredEquationOccurrenceSearch.RuleOrigin × Pattern)
    (present : answer ∈ ((model ambient allowed).firings source).answers) :
    Firing ambient allowed source answer.1 answer.2 := by
  cases decoded : decode ambient source with
  | none => simp [model, firingBatch, decoded] at present
  | some state =>
    have equal := decode_sound ambient source state decoded
    subst source
    simp only [model, firingBatch_state] at present
    exact ⟨state, rfl, AuthoredEquationOccurrenceSemantics.firings_sound (provider allowed) language FreeTypeContext.empty
      (ambientContext ambient) .proc _ answer.2 answer.1 present⟩

theorem firings_complete (ambient : Nat) (allowed : List Token) (source : Pattern)
    (_complete : ((model ambient allowed).firings source).unresolved = [])
    (origin : AuthoredEquationOccurrenceSearch.RuleOrigin) (target : Pattern)
    (firing : Firing ambient allowed source origin target) :
    (origin, target) ∈ ((model ambient allowed).firings source).answers := by
  obtain ⟨state, rfl, actual⟩ := firing
  simp only [model, firingBatch_state]
  exact AuthoredEquationOccurrenceSemantics.firings_complete (provider allowed) language FreeTypeContext.empty
    (ambientContext ambient) .proc rules_supported _ target origin actual

theorem equation_equiv_admitted (ambient : Nat) (allowed : List Token)
    {left right : Pattern} (equivalent : Relation.EqvGen (Equation ambient allowed) left right) :
    (∀ source : State ambient, left = source.pattern →
      ∃ target : State ambient, right = target.pattern ∧
        Relation.EqvGen (EquationEdge allowed) source target) ∧
    (∀ target : State ambient, right = target.pattern →
      ∃ source : State ambient, left = source.pattern ∧
        Relation.EqvGen (EquationEdge allowed) source target) := by
  induction equivalent with
  | rel left right edge =>
    obtain ⟨before, after, rfl, rfl, primitive⟩ := edge
    constructor
    · intro source same
      have equal := state_pattern_injective same
      subst before
      exact ⟨after, rfl, .rel _ _ primitive⟩
    · intro target same
      have equal := state_pattern_injective same
      subst after
      exact ⟨before, rfl, .rel _ _ primitive⟩
  | refl node =>
    constructor
    · intro source same
      exact ⟨source, same, .refl source⟩
    · intro target same
      exact ⟨target, same, .refl target⟩
  | symm left right equivalent ih =>
    constructor
    · intro source same
      obtain ⟨target, admitted, relation⟩ := ih.2 source same
      exact ⟨target, admitted, .symm _ _ relation⟩
    · intro target same
      obtain ⟨source, admitted, relation⟩ := ih.1 target same
      exact ⟨source, admitted, .symm _ _ relation⟩
  | trans left middle right first second firstIH secondIH =>
    constructor
    · intro source same
      obtain ⟨midpoint, admitted, firstRelation⟩ := firstIH.1 source same
      obtain ⟨target, admitted, secondRelation⟩ := secondIH.1 midpoint admitted
      exact ⟨target, admitted, .trans _ _ _ firstRelation secondRelation⟩
    · intro target same
      obtain ⟨midpoint, admitted, secondRelation⟩ := secondIH.2 target same
      obtain ⟨source, admitted, firstRelation⟩ := firstIH.2 midpoint admitted
      exact ⟨source, admitted, .trans _ _ _ firstRelation secondRelation⟩

theorem equation_equiv_embed {ambient : Nat} (allowed : List Token)
    {source target : State ambient} (equivalent : Relation.EqvGen (EquationEdge allowed) source target) :
    Relation.EqvGen (Equation ambient allowed) source.pattern target.pattern := by
  induction equivalent with
  | rel source target edge => exact .rel _ _ ⟨source, target, rfl, rfl, edge⟩
  | refl source => exact .refl _
  | symm source target relation ih => exact .symm _ _ ih
  | trans source middle target first second firstIH secondIH =>
    exact .trans _ _ _ firstIH secondIH

theorem equation_equiv_comparison {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    Relation.EqvGen (Equation ambient allowed) source.pattern target.pattern ↔
      Relation.EqvGen (EquationEdge allowed) source target := by
  constructor
  · intro equivalent
    obtain ⟨next, equal, relation⟩ := (equation_equiv_admitted ambient allowed equivalent).1 source rfl
    have same := state_pattern_injective equal
    subst next
    exact relation
  · exact equation_equiv_embed allowed

theorem firing_targets_comparison {ambient : Nat} (allowed : List Token)
    (source : State ambient) (target : Pattern) :
    (∃ origin, Firing ambient allowed source.pattern origin target) ↔
      ∃ (origin : EquationFrontierBinderProfile.Origin) (next : State ambient),
        EquationFrontierBinderProfile.Firing allowed source origin next ∧ target = next.pattern := by
  constructor
  · rintro ⟨origin, _, _, actual⟩
    have present := AuthoredEquationOccurrenceSemantics.firings_complete (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc rules_supported _ target origin actual
    exact (firingBatch_targets_semantics allowed ambient source target).mp ⟨origin, present⟩
  · intro finite
    obtain ⟨origin, present⟩ := (firingBatch_targets_semantics allowed ambient source target).mpr finite
    exact ⟨origin, source, rfl, AuthoredEquationOccurrenceSemantics.firings_sound
      (provider allowed) language FreeTypeContext.empty (ambientContext ambient) .proc
      source.pattern target origin present⟩

def Step (ambient : Nat) (allowed : List Token) : Pattern → Pattern → Prop :=
  FiniteEquationCoverage.ModuloStep (Equation ambient allowed)
    (fun source (answer : AuthoredEquationOccurrenceSearch.RuleOrigin × Pattern) =>
      Firing ambient allowed source answer.1 answer.2) Prod.snd

theorem step_comparison {ambient : Nat} (allowed : List Token) (source target : State ambient) :
    Step ambient allowed source.pattern target.pattern ↔
      EquationFrontierBinderProfile.Step allowed source target := by
  constructor
  · rintro ⟨rawRepresentative, ⟨origin, rawNext⟩, before, fire, after⟩
    obtain ⟨representative, representativeEq, beforeFinite⟩ :=
      (equation_equiv_admitted ambient allowed before).1 source rfl
    rw [representativeEq] at fire
    obtain ⟨finiteOrigin, next, primitive, nextEq⟩ :=
      (firing_targets_comparison allowed representative rawNext).mp ⟨origin, fire⟩
    rw [nextEq] at after
    exact ⟨representative, ⟨finiteOrigin, next⟩, beforeFinite, primitive,
      (equation_equiv_comparison allowed next target).mp after⟩
  · rintro ⟨representative, event, before, fire, after⟩
    obtain ⟨origin, actual⟩ := (firing_targets_comparison allowed representative event.target.pattern).mpr
      ⟨event.origin, event.target, fire, rfl⟩
    exact ⟨representative.pattern, (origin, event.target.pattern), equation_equiv_embed allowed before,
      actual, equation_equiv_embed allowed after⟩

theorem step_target_admitted {ambient : Nat} (allowed : List Token) (source : State ambient)
    (rawTarget : Pattern) (step : Step ambient allowed source.pattern rawTarget) :
    ∃ target : State ambient, rawTarget = target.pattern ∧
      EquationFrontierBinderProfile.Step allowed source target := by
  obtain ⟨rawRepresentative, ⟨origin, rawNext⟩, before, fire, after⟩ := step
  obtain ⟨representative, representativeEq, beforeFinite⟩ :=
    (equation_equiv_admitted ambient allowed before).1 source rfl
  rw [representativeEq] at fire
  obtain ⟨finiteOrigin, next, primitive, nextEq⟩ :=
    (firing_targets_comparison allowed representative rawNext).mp ⟨origin, fire⟩
  rw [nextEq] at after
  obtain ⟨target, targetEq, afterFinite⟩ := (equation_equiv_admitted ambient allowed after).1 next rfl
  exact ⟨target, targetEq, representative, ⟨finiteOrigin, next⟩, beforeFinite, primitive, afterFinite⟩

theorem generated_step_comparison {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    Step ambient allowed source.pattern target.pattern ↔
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.gsltModuloEquations
        (EquationFrontierBinderProfileGenerated.base allowed) language).Step
          source.pattern target.pattern := by
  rw [step_comparison]
  exact (EquationFrontierBinderProfileGenerated.generated_gslt_step_comparison allowed source target).symm

/-- The gate leaves every admitted authored answer unchanged; origin-level
soundness therefore checks the actual equation instance, not merely its edge. -/
theorem authored_equations_sound (ambient : Nat) (allowed : List Token)
    (source : Pattern) (answer : ConditionalEquationExecution.EquationReceipt × Pattern)
    (present : answer ∈ ((model ambient allowed).equations source).answers) :
    AuthoredEquationOccurrenceSemantics.Equation (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc answer.1 source answer.2 := by
  cases decoded : decode ambient source with
  | none => simp [model, equationBatch, decoded] at present
  | some state =>
    have equal := decode_sound ambient source state decoded
    subst source
    simp only [model, equationBatch_state] at present
    exact AuthoredEquationOccurrenceSemantics.equations_sound (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc _ answer.2 answer.1 present

theorem authored_firings_sound (ambient : Nat) (allowed : List Token)
    (source : Pattern) (answer : AuthoredEquationOccurrenceSearch.RuleOrigin × Pattern)
    (present : answer ∈ ((model ambient allowed).firings source).answers) :
    AuthoredEquationOccurrenceSemantics.Firing (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc source answer.1 answer.2 := by
  cases decoded : decode ambient source with
  | none => simp [model, firingBatch, decoded] at present
  | some state =>
    have equal := decode_sound ambient source state decoded
    subst source
    simp only [model, firingBatch_state] at present
    exact AuthoredEquationOccurrenceSemantics.firings_sound (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc _ answer.2 answer.1 present

/-- Every retained conversion, pending entry and emitted primitive is justified
by the independently authored, scoped-and-sorted instance semantics. -/
theorem authored_run_sound {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) :
    (execute allowed fuel source).Valid
      (AuthoredEquationOccurrenceSemantics.Equation (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc)
      (AuthoredEquationOccurrenceSemantics.Firing (provider allowed) language
        FreeTypeContext.empty (ambientContext ambient) .proc) source.pattern :=
  run_valid (model ambient allowed)
    (AuthoredEquationOccurrenceSemantics.Equation (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc)
    (AuthoredEquationOccurrenceSemantics.Firing (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc)
    (authored_equations_sound ambient allowed) (authored_firings_sound ambient allowed)
    source.pattern fuel (initial source.pattern) (initial_valid _ _ _)

theorem exact_resume {ambient : Nat} (allowed : List Token) (source : State ambient)
    (first second : Nat) :
    execute allowed (first + second) source =
      run (model ambient allowed) second (execute allowed first source) :=
  run_add (model ambient allowed) first second (initial source.pattern)

theorem preserves_complete_receipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (first second : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed first source).receipts) :
    receipt ∈ (execute allowed (first + second) source).receipts := by
  rw [exact_resume]
  exact run_preserves_receipt (model ambient allowed) second (execute allowed first source) receipt found

/-- A partial or exhaustive gated run enters the native receipt family with
its complete authored trace and ordered primitive origin still retained. -/
def nativeReceipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :
    EquationOccurrenceNativeReceipts.ReceiptFamily (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc source.pattern :=
  ⟨receipt, (authored_run_sound allowed source fuel).receipts receipt found⟩

def sortedNativeReceipt {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :=
  EquationOccurrenceNativeReceipts.sortedNative (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc
    (nativeReceipt allowed source fuel receipt found)

def interaction {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :=
  EquationOccurrenceNativeReceipts.asInteraction (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc
    (nativeReceipt allowed source fuel receipt found)

def history {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :=
  EquationOccurrenceNativeReceipts.history (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc
    (nativeReceipt allowed source fuel receipt found)

theorem emitted_one_primitive_event {ambient : Nat} (allowed : List Token)
    (source : State ambient) (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :
    (history allowed source fuel receipt found).length = 1 :=
  EquationOccurrenceNativeReceipts.history_primitive_count (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc _

theorem emitted_equation_administration {ambient : Nat} (allowed : List Token)
    (source : State ambient) (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :
    EquationOccurrenceNativeReceipts.administration (provider allowed) language
      FreeTypeContext.empty (ambientContext ambient) .proc
      (nativeReceipt allowed source fuel receipt found) = receipt.representative.conversions.length := rfl

theorem emitted_target_sorted {ambient : Nat} (allowed : List Token)
    (source : State ambient) (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :
    OpenPatternWellSorted language FreeTypeContext.empty (ambientContext ambient) .proc receipt.target :=
  (sortedNativeReceipt allowed source fuel receipt found).2.down

theorem emitted_complete_origin_readout {ambient : Nat} (allowed : List Token)
    (source : State ambient) (fuel : Nat) (receipt : EquationOccurrenceNativeReceipts.RuntimeReceipt)
    (found : receipt ∈ (execute allowed fuel source).receipts) :
    (interaction allowed source fuel receipt found).evidence.val.val.origin = receipt.origin ∧
      (interaction allowed source fuel receipt found).evidence.val.val.representative = receipt.representative :=
  EquationOccurrenceNativeReceipts.complete_origin_readout (provider allowed) language
    FreeTypeContext.empty (ambientContext ambient) .proc _

/-- Every partial result supplies the original complete scoped firing receipt;
quiescence is needed only for the converse coverage statement. -/
theorem receipt_sound {ambient : Nat} (allowed : List Token) (source : State ambient) (fuel : Nat)
    (receipt : Receipt Pattern ConditionalEquationExecution.EquationReceipt
      AuthoredEquationOccurrenceSearch.RuleOrigin)
    (present : receipt ∈ (execute allowed fuel source).receipts) :
    Relation.EqvGen (Equation ambient allowed) source.pattern receipt.representative.state ∧
      Firing ambient allowed receipt.representative.state receipt.origin receipt.target :=
  ResumableEquationCoverage.actual_receipt_sound (model ambient allowed) (Equation ambient allowed)
    (equations_sound ambient allowed) (Firing ambient allowed) (firings_sound ambient allowed)
    source.pattern fuel receipt present

theorem complete_endpoint_coverage {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (quiet : quiescent (execute allowed fuel source) = true) (target : Pattern) :
    (∃ receipt ∈ (execute allowed fuel source).receipts,
      Relation.EqvGen (Equation ambient allowed) receipt.target target) ↔
        Step ambient allowed source.pattern target :=
  ResumableEquationCoverage.actual_endpoint_coverage (model ambient allowed) (Equation ambient allowed)
    (equations_sound ambient allowed) (equations_complete ambient allowed) (Firing ambient allowed)
    (firings_sound ambient allowed) (firings_complete ambient allowed) source.pattern fuel quiet target

theorem complete_occurrence_coverage {ambient : Nat} (allowed : List Token)
    (source : State ambient) (fuel : Nat) (quiet : quiescent (execute allowed fuel source) = true)
    (representative target : Pattern) (origin : AuthoredEquationOccurrenceSearch.RuleOrigin)
    (before : Relation.EqvGen (Equation ambient allowed) source.pattern representative)
    (fire : Firing ambient allowed representative origin target) :
    ∃ entry index, entry ∈ (execute allowed fuel source).visited ∧ entry.state = representative ∧
      ((origin, target), index) ∈ ((model ambient allowed).firings representative).answers.zipIdx ∧
      (⟨entry, index, origin, target⟩ : Receipt Pattern ConditionalEquationExecution.EquationReceipt
        AuthoredEquationOccurrenceSearch.RuleOrigin) ∈ (execute allowed fuel source).receipts :=
  ResumableEquationCoverage.actual_firing_coverage (model ambient allowed) (Equation ambient allowed)
    (equations_sound ambient allowed) (equations_complete ambient allowed) (Firing ambient allowed)
    (firings_complete ambient allowed) source.pattern fuel quiet representative origin target before fire

theorem complete_generated_endpoint_coverage {ambient : Nat} (allowed : List Token)
    (source target : State ambient) (fuel : Nat)
    (quiet : quiescent (execute allowed fuel source) = true) :
    (∃ receipt ∈ (execute allowed fuel source).receipts,
      Relation.EqvGen (Equation ambient allowed) receipt.target target.pattern) ↔
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.gsltModuloEquations
        (EquationFrontierBinderProfileGenerated.base allowed) language).Step
          source.pattern target.pattern := by
  rw [complete_endpoint_coverage allowed source fuel quiet target.pattern]
  exact generated_step_comparison allowed source target

/-- Quotient endpoints forget equation presentations while primitive receipt
coverage continues to retain every distinct authored occurrence. -/
def classes {ambient : Nat} (allowed : List Token) (source : State ambient) (fuel : Nat) :
    List (Quotient (Relation.EqvGen.setoid (Equation ambient allowed))) :=
  ResumableEquationCoverage.actualClasses (model ambient allowed) (Equation ambient allowed)
    source.pattern fuel

theorem complete_class_coverage {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (quiet : quiescent (execute allowed fuel source) = true) (target : Pattern) :
    Quotient.mk (Relation.EqvGen.setoid (Equation ambient allowed)) target ∈
      classes allowed source fuel ↔ Step ambient allowed source.pattern target :=
  ResumableEquationCoverage.actual_class_coverage (model ambient allowed) (Equation ambient allowed)
    (equations_sound ambient allowed) (equations_complete ambient allowed) (Firing ambient allowed)
    (firings_sound ambient allowed) (firings_complete ambient allowed) source.pattern fuel quiet target

def targets {ambient : Nat} (allowed : List Token) (source : State ambient) (fuel : Nat) :
    List Pattern := (execute allowed fuel source).receipts.map Receipt.target

theorem complete_diamond {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (quiet : quiescent (execute allowed fuel source) = true) (test : Pattern → Bool)
    (invariant : ∀ initial next, Relation.EqvGen (Equation ambient allowed) initial next →
      test initial = test next) :
    (targets allowed source fuel).any test = true ↔
      ∃ next, Step ambient allowed source.pattern next ∧ test next = true :=
  ResumableEquationCoverage.actual_any_iff_diamond (model ambient allowed) (Equation ambient allowed)
    (equations_sound ambient allowed) (equations_complete ambient allowed) (Firing ambient allowed)
    (firings_sound ambient allowed) (firings_complete ambient allowed)
    source.pattern fuel quiet test invariant

theorem complete_outgoing_universal {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (quiet : quiescent (execute allowed fuel source) = true) (test : Pattern → Bool)
    (invariant : ∀ initial next, Relation.EqvGen (Equation ambient allowed) initial next →
      test initial = test next) :
    (targets allowed source fuel).all test = true ↔
      ∀ next, Step ambient allowed source.pattern next → test next = true :=
  ResumableEquationCoverage.actual_all_iff_outgoingUniversal (model ambient allowed) (Equation ambient allowed)
    (equations_sound ambient allowed) (equations_complete ambient allowed) (Firing ambient allowed)
    (firings_sound ambient allowed) (firings_complete ambient allowed)
    source.pattern fuel quiet test invariant

theorem complete_empty_iff_absent {ambient : Nat} (allowed : List Token) (source : State ambient)
    (fuel : Nat) (quiet : quiescent (execute allowed fuel source) = true) :
    (execute allowed fuel source).receipts = [] ↔ ¬ ∃ next, Step ambient allowed source.pattern next :=
  ResumableEquationCoverage.actual_empty_iff_no_step (model ambient allowed) (Equation ambient allowed)
    (equations_sound ambient allowed) (equations_complete ambient allowed) (Firing ambient allowed)
    (firings_sound ambient allowed) (firings_complete ambient allowed) source.pattern fuel quiet

/-- Queue entries whose representatives have already been scanned consume
work without rerunning their primitive occurrences. Their origins remain in
the previously emitted receipt list. -/
theorem run_drains_known {Node EqOrigin Occurrence Pending : Type} [DecidableEq Node]
    (executor : Model Node EqOrigin Occurrence Pending) (fuel : Nat)
    (snapshot : Snapshot Node EqOrigin Occurrence Pending)
    (known : ∀ entry ∈ snapshot.pending, entry.state ∈ snapshot.visited.map Entry.state)
    (enough : snapshot.pending.length ≤ fuel) :
    (run executor fuel snapshot).pending = [] ∧
      (run executor fuel snapshot).parked = snapshot.parked := by
  induction fuel generalizing snapshot with
  | zero =>
    have empty : snapshot.pending = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨empty, rfl⟩
  | succ fuel ih =>
    cases pending : snapshot.pending with
    | nil =>
      have unchanged : tick executor snapshot = snapshot := by simp [tick, pending]
      rw [run, unchanged]
      exact ih snapshot known (by simp [pending])
    | cons entry rest =>
      have seen := known entry (by simp [pending])
      have pendingAfter : (tick executor snapshot).pending = rest := by simp [tick, pending, seen]
      have visitedAfter : (tick executor snapshot).visited = snapshot.visited := by
        simp [tick, pending, seen]
      have parkedAfter : (tick executor snapshot).parked = snapshot.parked := by
        simp [tick, pending, seen]
      have remainingKnown : ∀ selected ∈ (tick executor snapshot).pending,
          selected.state ∈ (tick executor snapshot).visited.map Entry.state := by
        rw [pendingAfter, visitedAfter]
        intro selected member
        exact known selected (by simp [pending, member])
      have remainingEnough : (tick executor snapshot).pending.length ≤ fuel := by
        rw [pendingAfter]
        simp only [pending, List.length_cons] at enough
        omega
      obtain ⟨empty, parked⟩ := ih (tick executor snapshot) remainingKnown remainingEnough
      exact ⟨empty, parked.trans parkedAfter⟩

theorem neighbors_member_opposite {ambient : Nat} (allowed : List Token)
    (source target : State ambient) (member : target ∈ neighbors allowed source) :
    target = opposite source := by
  rcases source with ⟨phase, name, key⟩
  cases phase <;> by_cases enabled : key ∈ allowed <;>
    simp [neighbors, enabled] at member
  all_goals exact member

theorem opposite_involution {ambient : Nat} (state : State ambient) :
    opposite (opposite state) = state := by
  rcases state with ⟨phase, name, key⟩
  cases phase <;> rfl

theorem equation_answer_opposite {ambient : Nat} (allowed : List Token) (source : State ambient)
    (answer : ConditionalEquationExecution.EquationReceipt × Pattern)
    (member : answer ∈ ((model ambient allowed).equations source.pattern).answers) :
    answer.2 = (opposite source).pattern := by
  simp only [model, equationBatch_state] at member
  obtain ⟨target, equal, neighbor⟩ :=
    (equationBatch_targets_neighbors allowed ambient source answer.2).mp ⟨answer.1, member⟩
  exact equal.trans (congrArg State.pattern (neighbors_member_opposite allowed source target neighbor))

def firstScan {ambient : Nat} (allowed : List Token) (source : State ambient) :=
  tick (model ambient allowed) (initial source.pattern)

theorem firstScan_pending {ambient : Nat} (allowed : List Token) (source : State ambient) :
    (firstScan allowed source).pending =
      (discoveries (⟨source.pattern, []⟩ : Entry Pattern ConditionalEquationExecution.EquationReceipt)
        ((model ambient allowed).equations source.pattern).answers).filter
          (fun candidate => decide (candidate.state ∉ [source.pattern])) := by
  simp [firstScan, tick, initial]

theorem firstScan_visited {ambient : Nat} (allowed : List Token) (source : State ambient) :
    (firstScan allowed source).visited = [⟨source.pattern, []⟩] := by
  simp [firstScan, tick, initial]

theorem firstScan_parked {ambient : Nat} (allowed : List Token) (source : State ambient) :
    (firstScan allowed source).parked = [] := by
  have equationComplete : ((model ambient allowed).equations source.pattern).unresolved = [] := by
    simp only [model, equationBatch_state]
  have firingComplete : ((model ambient allowed).firings source.pattern).unresolved = [] := by
    simp only [model, firingBatch_state]
  simp [firstScan, tick, initial, equationComplete, firingComplete, obligations]

theorem firstScan_pending_opposite {ambient : Nat} (allowed : List Token) (source : State ambient)
    (entry : Entry Pattern ConditionalEquationExecution.EquationReceipt)
    (present : entry ∈ (firstScan allowed source).pending) : entry.state = (opposite source).pattern := by
  rw [firstScan_pending] at present
  obtain ⟨answer, member, equal⟩ := List.mem_map.mp (List.mem_filter.mp present).1
  cases equal
  exact equation_answer_opposite allowed source answer member

theorem secondScan_conditions {ambient : Nat} (allowed : List Token) (source : State ambient)
    (head : Entry Pattern ConditionalEquationExecution.EquationReceipt)
    (rest : List (Entry Pattern ConditionalEquationExecution.EquationReceipt))
    (pending : (firstScan allowed source).pending = head :: rest) :
    (tick (model ambient allowed) (firstScan allowed source)).pending = rest ∧
      (tick (model ambient allowed) (firstScan allowed source)).parked = [] ∧
      (∀ entry ∈ rest, entry.state ∈
        (tick (model ambient allowed) (firstScan allowed source)).visited.map Entry.state) := by
  have headState := firstScan_pending_opposite allowed source head (by simp [pending])
  have restStates : ∀ entry ∈ rest, entry.state = head.state := by
    intro entry member
    exact (firstScan_pending_opposite allowed source entry (by simp [pending, member])).trans headState.symm
  by_cases seen : head.state ∈ (firstScan allowed source).visited.map Entry.state
  · refine ⟨by simp [tick, pending, seen], by simp [tick, pending, seen, firstScan_parked], ?_⟩
    intro entry member
    simp only [tick, pending, seen, if_true]
    simpa only [restStates entry member] using seen
  · let known := head.state :: ((firstScan allowed source).visited.map Entry.state ++ rest.map Entry.state)
    have rootKnown : source.pattern ∈ known := by simp [known, firstScan_visited]
    have noNew : (discoveries head ((model ambient allowed).equations head.state).answers).filter
        (fun candidate => decide (candidate.state ∉ known)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro entry member
      obtain ⟨answer, actual, rfl⟩ := List.mem_map.mp member
      have back : answer.2 = source.pattern := by
        have atOpposite : answer ∈ ((model ambient allowed).equations (opposite source).pattern).answers :=
          headState ▸ actual
        simpa only [opposite_involution] using equation_answer_opposite allowed (opposite source) answer atOpposite
      simp [Entry.extend, back, rootKnown]
    have eqComplete : ((model ambient allowed).equations head.state).unresolved = [] := by
      rw [headState]
      simp only [model, equationBatch_state]
    have fireComplete : ((model ambient allowed).firings head.state).unresolved = [] := by
      rw [headState]
      simp only [model, firingBatch_state]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [tick, pending, seen, if_false, List.append_nil] using congrArg (rest ++ ·) noNew
    · simp [tick, pending, seen, firstScan_parked, eqComplete, fireComplete, obligations]
    · intro entry member
      simp only [tick, pending, seen, if_false, List.map_append, List.map_cons, List.map_nil,
        List.mem_append, List.mem_singleton]
      exact Or.inr (restStates entry member)

/-- The completion budget is computed from the first actual equation batch.
At most one new representative is scanned; duplicate conversion receipts may
take additional queue work but cannot create duplicate physical events. -/
def completionFuel {ambient : Nat} (allowed : List Token) (source : State ambient) : Nat :=
  1 + (firstScan allowed source).pending.length

theorem completion_quiescent {ambient : Nat} (allowed : List Token) (source : State ambient) :
    quiescent (execute allowed (completionFuel allowed source) source) = true := by
  change quiescent (run (model ambient allowed) (1 + (firstScan allowed source).pending.length)
    (initial source.pattern)) = true
  rw [run_add]
  change quiescent (run (model ambient allowed) (firstScan allowed source).pending.length
    (firstScan allowed source)) = true
  cases pending : (firstScan allowed source).pending with
  | nil => simp [run, pending, quiescent, firstScan_parked]
  | cons head rest =>
    obtain ⟨pendingAfter, parkedAfter, known⟩ := secondScan_conditions allowed source head rest pending
    have remainingKnown : ∀ entry ∈ (tick (model ambient allowed) (firstScan allowed source)).pending,
        entry.state ∈ (tick (model ambient allowed) (firstScan allowed source)).visited.map Entry.state := by
      simpa only [pendingAfter] using known
    have enough : (tick (model ambient allowed) (firstScan allowed source)).pending.length ≤ rest.length := by
      simp [pendingAfter]
    have drained := run_drains_known (model ambient allowed) rest.length
      (tick (model ambient allowed) (firstScan allowed source)) remainingKnown enough
    simp only [List.length_cons, run]
    rw [quiescent_iff]
    exact ⟨drained.1, drained.2.trans parkedAfter⟩

/-- The actual queue's retained walks form a computationally checked finite
certificate, independently of the separate static carrier certificate. -/
def completedCertificate {ambient : Nat} (allowed : List Token) (source : State ambient) :=
  ResumableEquationCoverage.coverageCertificate
    (execute allowed (completionFuel allowed source) source)

theorem completed_certificate_checked {ambient : Nat} (allowed : List Token)
    (source : State ambient) :
    (completedCertificate allowed source).check
      (ResumableEquationCoverage.equationNeighbors (model ambient allowed)) source.pattern = true :=
  ResumableEquationCoverage.quiescent_run_certificate_checked (model ambient allowed)
    source.pattern (completionFuel allowed source) (completion_quiescent allowed source)

theorem completed_representative_coverage {ambient : Nat} (allowed : List Token)
    (source : State ambient) (representative : Pattern) :
    representative ∈ (execute allowed (completionFuel allowed source) source).visited.map Entry.state ↔
      Relation.EqvGen (Equation ambient allowed) source.pattern representative :=
  ResumableEquationCoverage.quiescent_visited_iff_equivalent (model ambient allowed)
    (Equation ambient allowed) (equations_sound ambient allowed) (equations_complete ambient allowed)
    source.pattern (completionFuel allowed source) (completion_quiescent allowed source) representative

/-- The completed actual queue, for this whole typed family, is a semantic
frontier without an external completeness assumption. -/
theorem completed_generated_endpoint_coverage {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    (∃ receipt ∈ (execute allowed (completionFuel allowed source) source).receipts,
      Relation.EqvGen (Equation ambient allowed) receipt.target target.pattern) ↔
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.gsltModuloEquations
        (EquationFrontierBinderProfileGenerated.base allowed) language).Step
          source.pattern target.pattern :=
  complete_generated_endpoint_coverage allowed source target (completionFuel allowed source)
    (completion_quiescent allowed source)

theorem completed_occurrence_coverage {ambient : Nat} (allowed : List Token)
    (source : State ambient) (representative target : Pattern)
    (origin : AuthoredEquationOccurrenceSearch.RuleOrigin)
    (before : Relation.EqvGen (Equation ambient allowed) source.pattern representative)
    (fire : Firing ambient allowed representative origin target) :
    ∃ entry index, entry ∈ (execute allowed (completionFuel allowed source) source).visited ∧
      entry.state = representative ∧
      ((origin, target), index) ∈ ((model ambient allowed).firings representative).answers.zipIdx ∧
      (⟨entry, index, origin, target⟩ : Receipt Pattern ConditionalEquationExecution.EquationReceipt
        AuthoredEquationOccurrenceSearch.RuleOrigin) ∈
          (execute allowed (completionFuel allowed source) source).receipts :=
  complete_occurrence_coverage allowed source (completionFuel allowed source)
    (completion_quiescent allowed source) representative target origin before fire

theorem completed_class_coverage {ambient : Nat} (allowed : List Token) (source : State ambient)
    (target : Pattern) :
    Quotient.mk (Relation.EqvGen.setoid (Equation ambient allowed)) target ∈
      classes allowed source (completionFuel allowed source) ↔
        Step ambient allowed source.pattern target :=
  complete_class_coverage allowed source (completionFuel allowed source)
    (completion_quiescent allowed source) target

theorem completed_generated_class_coverage {ambient : Nat} (allowed : List Token)
    (source target : State ambient) :
    Quotient.mk (Relation.EqvGen.setoid (Equation ambient allowed)) target.pattern ∈
      classes allowed source (completionFuel allowed source) ↔
      (Mettapedia.GSLT.LanguageDef.EquationSemantics.gsltModuloEquations
        (EquationFrontierBinderProfileGenerated.base allowed) language).Step
          source.pattern target.pattern := by
  rw [completed_class_coverage allowed source target.pattern]
  exact generated_step_comparison allowed source target

theorem completed_diamond {ambient : Nat} (allowed : List Token) (source : State ambient)
    (test : Pattern → Bool)
    (invariant : ∀ initial next, Relation.EqvGen (Equation ambient allowed) initial next →
      test initial = test next) :
    (targets allowed source (completionFuel allowed source)).any test = true ↔
      ∃ next, Step ambient allowed source.pattern next ∧ test next = true :=
  complete_diamond allowed source (completionFuel allowed source) (completion_quiescent allowed source)
    test invariant

theorem completed_outgoing_universal {ambient : Nat} (allowed : List Token) (source : State ambient)
    (test : Pattern → Bool)
    (invariant : ∀ initial next, Relation.EqvGen (Equation ambient allowed) initial next →
      test initial = test next) :
    (targets allowed source (completionFuel allowed source)).all test = true ↔
      ∀ next, Step ambient allowed source.pattern next → test next = true :=
  complete_outgoing_universal allowed source (completionFuel allowed source) (completion_quiescent allowed source)
    test invariant

theorem completed_empty_iff_absent {ambient : Nat} (allowed : List Token) (source : State ambient) :
    (execute allowed (completionFuel allowed source) source).receipts = [] ↔
      ¬ ∃ next, Step ambient allowed source.pattern next :=
  complete_empty_iff_absent allowed source (completionFuel allowed source) (completion_quiescent allowed source)

end Mettapedia.OSLF.MeTTaIL.EquationFrontierBinderCertifiedSearch
