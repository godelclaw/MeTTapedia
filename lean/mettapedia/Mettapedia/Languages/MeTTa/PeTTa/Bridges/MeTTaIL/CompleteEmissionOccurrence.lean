import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSearch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.CollectionOccurrence

/-!
# Certified nested occurrence execution through the common emitter

The bounded admission certificate supplies source coverage and local rule
readiness. Its realization feeds the existing emitted entry bodies; source
receipts and raw retained occurrence evidence remain available separately.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (declaredFootprint)
open Mettapedia.Machines.ResumableSearchRunner (Machine)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval WireKit
open CompleteExecution (patternValue)
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The selected profile retains free-context validation. Compiled admission
therefore supplies the finite native table used by every emitted entry. -/
theorem footprinted_of_occurrence_compiled
    {snapshot : GeneralExecutionAdmission.Snapshot} {permissions : GeneralExecutionAdmission.Permissions}
    (certificate : CollectionOccurrenceAdmission.Certificate (GeneralExecutionAdmission.compile snapshot permissions))
    (bound : List TypeExpr) (expected : TypeExpr) (mode : Complete.Normalized.Commit) :
    Footprinted ⟨GeneralExecutionAdmission.compile snapshot permissions, bound, expected, mode⟩ := by
  have free : GeneralExecutionAdmission.checkFreeContext snapshot = true := by
    by_contra failed
    have bad : GeneralExecutionAdmission.Obligation.invalidFreeContext ∈
        (GeneralExecutionAdmission.compile snapshot permissions).obligations := by
      simp [GeneralExecutionAdmission.compile, Bool.eq_false_iff.mpr failed]
    have kept : GeneralExecutionAdmission.Obligation.invalidFreeContext ∈
        CollectionOccurrenceAdmission.pending (GeneralExecutionAdmission.compile snapshot permissions) :=
      List.mem_filter.mpr ⟨bad, by decide⟩
    rw [certificate.requirements.pending] at kept
    cases kept
  refine ⟨Complete.Footprint.declared_scope certificate.requirements.finiteProvider ?_, ?_⟩
  · intro equation member
    rw [certificate.requirements.noEquations] at member
    cases member
  · simpa only [GeneralExecutionAdmission.compile, GeneralExecutionAdmission.checkFreeContext, decide_eq_true_eq] using
      (Bool.and_eq_true_iff.mp free).1

variable {spec : Spec} (certificate : CollectionOccurrenceAdmission.Certificate spec.plan)
    (canonical : spec.mode = .canonical) (footprinted : Footprinted spec)

abbrev occurrenceSearch (spec : Spec) :=
  CollectionOccurrenceSearch.search spec.plan spec.bound spec.expected 0

def occurrenceRealization := CompleteExecution.CollectionOccurrence.realization
  (bound := spec.bound) (expected := spec.expected)
  (table spec) (table_for spec) (declaredFootprint spec.plan) footprinted.scope
  certificate.requirements.admitted 0

private theorem occurrence_backend_eq :
    (occurrenceRealization certificate footprinted).backend =
      backendAtom spec (.collectionOccurrence certificate canonical) := rfl

private theorem occurrence_plan_eq : (occurrenceRealization certificate footprinted).plan = planAtom spec := by
  change encoded (CompletePlanWire.planTerm spec.plan
    (spec.plan.snapshot.free.entriesOn (declaredFootprint spec.plan)) spec.bound spec.expected) = _
  rw [← footprinted.tabled]
  rfl

include canonical in
private theorem occurrence_standard_eq : (occurrenceRealization certificate footprinted).standard = standardAtom spec := by
  simp only [occurrenceRealization, CompleteExecution.CollectionOccurrence.realization, standardAtom, canonical,
    StandardWire.commitTerm, StandardWire.canonicalTerm, certificate.requirements.noLaws, certificate.requirements.noExtrusions, encodeList]

private theorem occurrence_source_ready (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) :
    (occurrenceRealization certificate footprinted).SourceReady (CanonicalBags.canon source) :=
  checkOpenPatternWellSorted_complete (CanonicalBags.openPatternWellSorted_canon typed)

include canonical in
private theorem occurrence_prepared (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) :
    PureReturns runtime [] state
      (apply "gslt:runner:standard" [(occurrenceRealization certificate footprinted).standard, patternValue source])
      state (patternValue (CanonicalBags.canon source)) := by
  have checked : Complete.Classes.Checked spec.plan spec.bound spec.expected source := checkOpenPatternWellSorted_complete typed
  have ready : CompleteExecution.CommitReady spec.mode (table spec) source :=
    CompleteExecution.commitReady_of_checked spec.plan (table_for spec) checked
  have native := CompleteExecution.runner_standard_returns spec.plan state spec.mode (table spec) (table_for spec)
    source ready
  have commitEq : Complete.Normalized.commit spec.plan spec.mode source = CanonicalBags.canon source := by
    simp only [canonical, Complete.Normalized.commit, Complete.Normalized.standard,
      certificate.requirements.noLaws, certificate.requirements.noExtrusions, CollectionLaws.standardForm_nil]
  simpa only [occurrence_standard_eq certificate canonical footprinted, standardAtom, commitEq] using native

include footprinted

theorem occurrence_begin_entry_returns {name : String}
    (fresh : namesFresh spec name (.collectionOccurrence certificate canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) :
    PureReturns (emittedRuntime spec name (.collectionOccurrence certificate canonical)) [] state
      (apply (beginHead name) [patternValue source]) state
      (encoded ((occurrenceRealization certificate footprinted).machineTerm
        (Machine.begin (occurrenceSearch spec) (CanonicalBags.canon source)))) := by
  exact begin_entry_of_realization (.collectionOccurrence certificate canonical)
    (occurrenceRealization certificate footprinted) (occurrence_backend_eq certificate canonical footprinted)
    (occurrence_plan_eq certificate footprinted) (occurrence_standard_eq certificate canonical footprinted)
    fresh state source _ (occurrence_source_ready certificate footprinted source typed)
    (occurrence_prepared certificate canonical footprinted state source typed)

theorem occurrence_run_entry_returns {name : String}
    (fresh : namesFresh spec name (.collectionOccurrence certificate canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) (ticks quantum : Nat) :
    PureReturns (emittedRuntime spec name (.collectionOccurrence certificate canonical)) [] state
      (apply (runHead name) [patternValue source, number ticks, number quantum]) state
      (encoded (CompleteExecution.SearchWire.traceTerm
        (Machine.advance (occurrenceSearch spec) ticks quantum
          (Machine.begin (occurrenceSearch spec) (CanonicalBags.canon source))))) := by
  exact run_entry_of_realization (.collectionOccurrence certificate canonical)
    (occurrenceRealization certificate footprinted) (occurrence_backend_eq certificate canonical footprinted)
    (occurrence_plan_eq certificate footprinted) (occurrence_standard_eq certificate canonical footprinted)
    fresh state source _ (occurrence_source_ready certificate footprinted source typed)
    (occurrence_prepared certificate canonical footprinted state source typed) ticks quantum

theorem occurrence_explore_entry_returns {name : String}
    (fresh : namesFresh spec name (.collectionOccurrence certificate canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) (work : Nat) :
    PureReturns (emittedRuntime spec name (.collectionOccurrence certificate canonical)) [] state
      (apply (exploreHead name) [patternValue source, number work]) state
      (CompleteExecution.patternsValue ((Complete.Settled.roundsUntilSettled (occurrenceSearch spec) work
        (Complete.Explore.begin (occurrenceSearch spec) (CanonicalBags.canon source))).nodes.map (·.state))) := by
  exact explore_entry_of_realization (.collectionOccurrence certificate canonical)
    (occurrenceRealization certificate footprinted) (occurrence_backend_eq certificate canonical footprinted)
    (occurrence_plan_eq certificate footprinted) (occurrence_standard_eq certificate canonical footprinted)
    fresh state source _ (occurrence_source_ready certificate footprinted source typed)
    (occurrence_prepared certificate canonical footprinted state source typed) work

theorem occurrence_edges_entry_returns {name : String}
    (fresh : namesFresh spec name (.collectionOccurrence certificate canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) (work : Nat) :
    PureReturns (emittedRuntime spec name (.collectionOccurrence certificate canonical)) [] state
      (apply (edgesHead name) [patternValue source, number work]) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm ScopedRuleJobReadoutExecution.receiptTerm)
        (Complete.Graph.edges (occurrenceSearch spec)
          (Complete.Settled.roundsUntilSettled (occurrenceSearch spec) work
            (Complete.Explore.begin (occurrenceSearch spec) (CanonicalBags.canon source)))))) := by
  exact edges_entry_of_realization (.collectionOccurrence certificate canonical)
    (occurrenceRealization certificate footprinted) (occurrence_backend_eq certificate canonical footprinted)
    (occurrence_plan_eq certificate footprinted) (occurrence_standard_eq certificate canonical footprinted)
    fresh state source _ (occurrence_source_ready certificate footprinted source typed)
    (occurrence_prepared certificate canonical footprinted state source typed) work

/-- Finite emitted pages retain a source-step chain, independently of whether
the search has completed. -/
theorem occurrence_emitted_run_contract {name : String}
    (fresh : namesFresh spec name (.collectionOccurrence certificate canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) (ticks quantum : Nat) :
    let machine := Machine.advance (occurrenceSearch spec) ticks quantum
      (Machine.begin (occurrenceSearch spec) (CanonicalBags.canon source))
    PureReturns (emittedRuntime spec name (.collectionOccurrence certificate canonical)) [] state
      (apply (runHead name) [patternValue source, number ticks, number quantum]) state
      (encoded (CompleteExecution.SearchWire.traceTerm machine)) ∧
    machine.states.reverse.head? = some (CanonicalBags.canon source) ∧
    machine.states.reverse.IsChain (Complete.Presented.gslt spec.plan spec.bound spec.expected).Step := by
  refine ⟨occurrence_run_entry_returns certificate canonical footprinted fresh state source typed ticks quantum, ?_⟩
  exact Mettapedia.Machines.ResumableSearchRunner.run_chain
    (CollectionOccurrenceSearch.search_lawful spec.plan spec.bound spec.expected 0)
    (fun valid => valid) (CanonicalBags.canon source) ticks quantum

/-- Actual emitted edges are source steps. Once settled, the same graph
contains exactly the canonical successor classes of every explored node.
Receipts remain a list; this theorem makes no derivation-count identification. -/
theorem occurrence_emitted_graph_contract {name : String}
    (fresh : namesFresh spec name (.collectionOccurrence certificate canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free spec.bound spec.expected source) (work : Nat) :
    let final := Complete.Settled.roundsUntilSettled (occurrenceSearch spec) work
      (Complete.Explore.begin (occurrenceSearch spec) (CanonicalBags.canon source))
    PureReturns (emittedRuntime spec name (.collectionOccurrence certificate canonical)) [] state
      (apply (edgesHead name) [patternValue source, number work]) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm ScopedRuleJobReadoutExecution.receiptTerm)
        (Complete.Graph.edges (occurrenceSearch spec) final))) ∧
    (∀ edge ∈ Complete.Graph.edges (occurrenceSearch spec) final,
      (Complete.Presented.gslt spec.plan spec.bound spec.expected).Step edge.1 edge.2.2) ∧
    (Complete.Settled.settled (occurrenceSearch spec) final = true →
      ∀ node ∈ final.nodes, ∀ target,
        (Complete.Presented.gslt spec.plan spec.bound spec.expected).Step node.state (CanonicalBags.canon target) ↔
          ∃ receipt, (node.state, receipt, CanonicalBags.canon target) ∈
            Complete.Graph.edges (occurrenceSearch spec) final) := by
  dsimp only
  refine ⟨occurrence_edges_entry_returns certificate canonical footprinted fresh state source typed work, ?_⟩
  obtain ⟨spent, _, reached⟩ := Complete.Graph.roundsUntilSettled_explore
    (S := occurrenceSearch spec) (CanonicalBags.canon source) work 0
  simp only [Nat.zero_add] at reached
  change Complete.Settled.roundsUntilSettled (occurrenceSearch spec) work
    (Complete.Explore.begin (occurrenceSearch spec) (CanonicalBags.canon source)) =
    Complete.Explore.explore (occurrenceSearch spec) (CanonicalBags.canon source) spent at reached
  rw [reached]
  have edgeSound := Complete.Graph.edge_valid
    (CollectionOccurrenceSearch.search_lawful spec.plan spec.bound spec.expected 0)
    (CanonicalBags.canon source) spent
  constructor
  · intro edge member
    obtain ⟨valid, targetEq⟩ := edgeSound edge member
    rw [targetEq]
    exact valid
  · intro done node member target
    constructor
    · intro stepped
      obtain ⟨receipt, target', edge, same⟩ :=
        CollectionOccurrenceAdmission.settled_edges_cover_steps certificate spec.bound spec.expected 0
          (CanonicalBags.canon source) spent done node member (CanonicalBags.canon target) stepped
      have targetEq := (edgeSound _ edge).2
      change target' = CanonicalBags.canon receipt.target at targetEq
      have targetCanonical : CanonicalBags.canon target' = target' := by
        rw [targetEq, CanonicalBags.canon_idempotent]
      have canonicalTarget : CanonicalBags.canon target = target' := by
        simpa only [CanonicalBags.Same, CanonicalBags.canon_idempotent, targetCanonical] using same
      rw [← canonicalTarget] at edge
      exact ⟨receipt, edge⟩
    · rintro ⟨receipt, edge⟩
      obtain ⟨valid, targetEq⟩ := edgeSound _ edge
      change CanonicalBags.canon target = CanonicalBags.canon receipt.target at targetEq
      change (Complete.Presented.gslt spec.plan spec.bound spec.expected).Step
        node.state (CanonicalBags.canon receipt.target) at valid
      rwa [← targetEq] at valid

omit footprinted

/-- The established root profile keeps precedence. Otherwise recognition of
the occurrence profile selects it without inspecting language names. -/
theorem admittedProfile_occurrence
    (noRoot : spec.bound = [] → CollectionRootSearch.coverageProfile? spec.plan = none)
    (recognized : CollectionOccurrenceAdmission.admit? spec.plan = some certificate) :
    admittedProfile spec = .collectionOccurrence certificate canonical := by
  unfold admittedProfile
  simp only [dif_pos canonical]
  split
  · rename_i closed
    rw [noRoot closed, recognized]
  · rw [recognized]

abbrev compiledOccurrenceSpec (snapshot : GeneralExecutionAdmission.Snapshot)
    (permissions : GeneralExecutionAdmission.Permissions) (bound : List TypeExpr) (expected : TypeExpr) : Spec :=
  ⟨GeneralExecutionAdmission.compile snapshot permissions, bound, expected, .canonical⟩

/-- Admission-to-native graph execution for the actual selected compiled
profile. Readiness and source coverage are consequences of its checked
admission conditions, rather than additional theorem-valued inputs. -/
theorem emitted_occurrence_compiled_graph
    {snapshot : GeneralExecutionAdmission.Snapshot} {permissions : GeneralExecutionAdmission.Permissions}
    (certificate : CollectionOccurrenceAdmission.Certificate (GeneralExecutionAdmission.compile snapshot permissions))
    (bound : List TypeExpr) (expected : TypeExpr)
    (noRoot : bound = [] → CollectionRootSearch.coverageProfile?
      (GeneralExecutionAdmission.compile snapshot permissions) = none)
    (recognized : CollectionOccurrenceAdmission.admit? (GeneralExecutionAdmission.compile snapshot permissions) =
      some certificate) {name : String} {emitted : SpaceSemantics.Program}
    (accepted : emit? (compiledOccurrenceSpec snapshot permissions bound expected) name = .ok emitted)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)).language
      snapshot.free bound expected source) (work : Nat) :
    let spec := compiledOccurrenceSpec snapshot permissions bound expected
    let search := occurrenceSearch spec
    let final := Complete.Settled.roundsUntilSettled search work
      (Complete.Explore.begin search (CanonicalBags.canon source))
    PureReturns (runtime.append emitted) [] state
      (apply (edgesHead name) [patternValue source, number work]) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm ScopedRuleJobReadoutExecution.receiptTerm)
        (Complete.Graph.edges search final))) ∧
    (∀ edge ∈ Complete.Graph.edges search final,
      (Complete.Presented.gslt spec.plan bound expected).Step edge.1 edge.2.2) ∧
    (Complete.Settled.settled search final = true →
      ∀ node ∈ final.nodes, ∀ target,
        (Complete.Presented.gslt spec.plan bound expected).Step node.state (CanonicalBags.canon target) ↔
          ∃ receipt, (node.state, receipt, CanonicalBags.canon target) ∈ Complete.Graph.edges search final) := by
  have chosen := admittedProfile_occurrence
    (spec := compiledOccurrenceSpec snapshot permissions bound expected) certificate rfl noRoot recognized
  change emit? _ name (admittedProfile _) = .ok emitted at accepted
  rw [chosen] at accepted
  obtain ⟨rfl, admitted⟩ := emit?_ok accepted
  exact occurrence_emitted_graph_contract certificate rfl
    (footprinted_of_occurrence_compiled certificate bound expected .canonical) admitted.fresh state source typed work

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
