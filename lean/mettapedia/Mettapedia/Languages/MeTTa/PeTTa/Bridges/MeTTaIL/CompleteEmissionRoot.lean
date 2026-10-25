import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionSearch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionRootCoverageExecution

/-!
# Certified root collections through the common emitter

The ordinary emitter's selected profile is realized by the existing native
root search. Its entries inherit the shared runner and explorer theorems.
The source plan retains its capability obligations. Emission discharges root
set matching only through the selected certified profile.
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

theorem admittedProfile_root {spec : Spec}
    (certificate : CollectionRootSearch.CoverageProfile spec.plan)
    (closed : spec.bound = []) (canonical : spec.mode = .canonical)
    (recognized : CollectionRootSearch.coverageProfile? spec.plan = some certificate) :
    admittedProfile spec = .rootCollection certificate closed canonical := by
  simp [admittedProfile, closed, canonical, recognized]

/-- Every emitted descriptor belongs to the common certified interface.
The historical direct-publication search is never selected by the emitter. -/
theorem emitter_excludes_legacy_search (spec : Spec) (profile : SearchProfile spec) (names : List String) :
    backendAtom spec profile ≠ CettaWireAtom.encode
      (.application "CollectionSearch" [encodeList Term.string names]) := by
  cases profile <;> simp [backendAtom, CompleteExecution.classSearchBackend, CettaWireAtom.encode]

/-- Compiled root admission supplies native footprint readiness as well as
source coverage. A rejected free-name table cannot be hidden by discharging
the separate set-matching obligation. -/
theorem footprinted_of_root_compiled
    {snapshot : GeneralExecutionAdmission.Snapshot} {permissions : GeneralExecutionAdmission.Permissions}
    (certificate : CollectionRootSearch.CoverageProfile (GeneralExecutionAdmission.compile snapshot permissions))
    (bound : List TypeExpr) (expected : TypeExpr) (mode : Complete.Normalized.Commit) :
    Footprinted ⟨GeneralExecutionAdmission.compile snapshot permissions, bound, expected, mode⟩ := by
  have free : GeneralExecutionAdmission.checkFreeContext snapshot = true := by
    by_contra failed
    have bad : GeneralExecutionAdmission.Obligation.invalidFreeContext ∈
        (GeneralExecutionAdmission.compile snapshot permissions).obligations := by
      simp [GeneralExecutionAdmission.compile, Bool.eq_false_iff.mpr failed]
    have kept : GeneralExecutionAdmission.Obligation.invalidFreeContext ∈
        CollectionExecutionAdmission.inheritedObligations
          (GeneralExecutionAdmission.compile snapshot permissions) :=
      List.mem_filter.mpr ⟨bad, by decide⟩
    rw [CollectionExecutionAdmission.inherited_discharged certificate.profile.collection] at kept
    cases kept
  refine ⟨Complete.Footprint.declared_scope certificate.profile.finiteProvider ?_, ?_⟩
  · intro equation member
    rw [certificate.profile.noEquations] at member
    cases member
  · simpa only [GeneralExecutionAdmission.compile, GeneralExecutionAdmission.checkFreeContext, decide_eq_true_eq] using
      (Bool.and_eq_true_iff.mp free).1

variable {spec : Spec} (certificate : CollectionRootSearch.CoverageProfile spec.plan)
    (closed : spec.bound = []) (canonical : spec.mode = .canonical) (footprinted : Footprinted spec)

abbrev rootSearch := CollectionRootSearch.search (profile := certificate.profile) spec.expected

def rootRealization := CompleteExecution.RootCollection.realization
  (profile := certificate.profile) (expected := spec.expected)
  (table spec) (table_for spec) (declaredFootprint spec.plan) footprinted.scope

private theorem root_backend_eq :
    (rootRealization certificate footprinted).backend =
      backendAtom spec (.rootCollection certificate closed canonical) := rfl

include closed in
private theorem root_plan_eq : (rootRealization certificate footprinted).plan = planAtom spec := by
  change CompleteExecution.planValue spec.plan
    (spec.plan.snapshot.free.entriesOn (declaredFootprint spec.plan)) [] spec.expected = _
  rw [← footprinted.tabled, ← closed]
  rfl

include canonical in
private theorem root_standard_eq : (rootRealization certificate footprinted).standard = standardAtom spec := by
  simp only [rootRealization, CompleteExecution.RootCollection.realization, standardAtom, canonical,
    StandardWire.commitTerm, StandardWire.canonicalTerm, certificate.noLaws, certificate.noExtrusions, encodeList]

private theorem root_source_ready (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan) :
    (rootRealization certificate footprinted).SourceReady (CanonicalBags.canon source) :=
  ⟨fun name member => inside name ((CanonicalBags.canon_freeFvarNames source name).mp member),
    CollectionRequestExecution.arrangedRoot_canon source⟩

include canonical in
private theorem root_prepared (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) :
    PureReturns runtime [] state
      (apply "gslt:runner:standard" [(rootRealization certificate footprinted).standard, patternValue source])
      state (patternValue (CanonicalBags.canon source)) := by
  have checked : Complete.Classes.Checked spec.plan [] spec.expected source := checkOpenPatternWellSorted_complete typed
  have ready : CompleteExecution.CommitReady spec.mode (table spec) source :=
    CompleteExecution.commitReady_of_checked spec.plan (table_for spec) checked
  have native := CompleteExecution.runner_standard_returns spec.plan state spec.mode (table spec) (table_for spec)
    source ready
  have commitEq : Complete.Normalized.commit spec.plan spec.mode source = CanonicalBags.canon source := by
    simp only [canonical, Complete.Normalized.commit, Complete.Normalized.standard,
      certificate.noLaws, certificate.noExtrusions, CollectionLaws.standardForm_nil]
  simpa only [root_standard_eq certificate canonical footprinted, standardAtom, commitEq] using native

include footprinted

private theorem root_inside (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) :
    ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan :=
  Complete.Footprint.sorted_within footprinted.scope.declared (checkOpenPatternWellSorted_complete typed)

theorem root_begin_entry_returns {name : String}
    (fresh : namesFresh spec name (.rootCollection certificate closed canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) :
    PureReturns (emittedRuntime spec name (.rootCollection certificate closed canonical)) [] state
      (apply (beginHead name) [patternValue source]) state
      (encoded ((rootRealization certificate footprinted).machineTerm
        (Machine.begin (rootSearch certificate) (CanonicalBags.canon source)))) := by
  exact begin_entry_of_realization (.rootCollection certificate closed canonical)
    (rootRealization certificate footprinted) (root_backend_eq certificate closed canonical footprinted)
    (root_plan_eq certificate closed footprinted) (root_standard_eq certificate canonical footprinted)
    fresh state source _ (root_source_ready certificate footprinted source (root_inside footprinted source typed))
    (root_prepared certificate canonical footprinted state source typed)

theorem root_run_entry_returns {name : String}
    (fresh : namesFresh spec name (.rootCollection certificate closed canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) (ticks quantum : Nat) :
    PureReturns (emittedRuntime spec name (.rootCollection certificate closed canonical)) [] state
      (apply (runHead name) [patternValue source, number ticks, number quantum]) state
      (encoded (CompleteExecution.SearchWire.traceTerm
        (Machine.advance (rootSearch certificate) ticks quantum
          (Machine.begin (rootSearch certificate) (CanonicalBags.canon source))))) := by
  exact run_entry_of_realization (.rootCollection certificate closed canonical)
    (rootRealization certificate footprinted) (root_backend_eq certificate closed canonical footprinted)
    (root_plan_eq certificate closed footprinted) (root_standard_eq certificate canonical footprinted)
    fresh state source _ (root_source_ready certificate footprinted source (root_inside footprinted source typed))
    (root_prepared certificate canonical footprinted state source typed) ticks quantum

theorem root_explore_entry_returns {name : String}
    (fresh : namesFresh spec name (.rootCollection certificate closed canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) (work : Nat) :
    PureReturns (emittedRuntime spec name (.rootCollection certificate closed canonical)) [] state
      (apply (exploreHead name) [patternValue source, number work]) state
      (CompleteExecution.patternsValue ((Complete.Settled.roundsUntilSettled (rootSearch certificate) work
        (Complete.Explore.begin (rootSearch certificate) (CanonicalBags.canon source))).nodes.map (·.state))) := by
  exact explore_entry_of_realization (.rootCollection certificate closed canonical)
    (rootRealization certificate footprinted) (root_backend_eq certificate closed canonical footprinted)
    (root_plan_eq certificate closed footprinted) (root_standard_eq certificate canonical footprinted)
    fresh state source _ (root_source_ready certificate footprinted source (root_inside footprinted source typed))
    (root_prepared certificate canonical footprinted state source typed) work

theorem root_edges_entry_returns {name : String}
    (fresh : namesFresh spec name (.rootCollection certificate closed canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) (work : Nat) :
    PureReturns (emittedRuntime spec name (.rootCollection certificate closed canonical)) [] state
      (apply (edgesHead name) [patternValue source, number work]) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm CompleteExecution.RootCollection.receiptTerm)
        (Complete.Graph.edges (rootSearch certificate)
          (Complete.Settled.roundsUntilSettled (rootSearch certificate) work
            (Complete.Explore.begin (rootSearch certificate) (CanonicalBags.canon source)))))) := by
  exact edges_entry_of_realization (.rootCollection certificate closed canonical)
    (rootRealization certificate footprinted) (root_backend_eq certificate closed canonical footprinted)
    (root_plan_eq certificate closed footprinted) (root_standard_eq certificate canonical footprinted)
    fresh state source _ (root_source_ready certificate footprinted source (root_inside footprinted source typed))
    (root_prepared certificate canonical footprinted state source typed) work

/-- Emitted runs are actual chains in the source GSLT. No termination or
scheduler-fairness claim is inferred from this finite-page correspondence. -/
theorem root_emitted_run_contract {name : String}
    (fresh : namesFresh spec name (.rootCollection certificate closed canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) (ticks quantum : Nat) :
    let machine := Machine.advance (rootSearch certificate) ticks quantum
      (Machine.begin (rootSearch certificate) (CanonicalBags.canon source))
    PureReturns (emittedRuntime spec name (.rootCollection certificate closed canonical)) [] state
      (apply (runHead name) [patternValue source, number ticks, number quantum]) state
      (encoded (CompleteExecution.SearchWire.traceTerm machine)) ∧
    machine.states.reverse.head? = some (CanonicalBags.canon source) ∧
    machine.states.reverse.IsChain (Complete.Presented.gslt spec.plan [] spec.expected).Step := by
  refine ⟨root_run_entry_returns certificate closed canonical footprinted fresh state source typed ticks quantum, ?_⟩
  exact Mettapedia.Machines.ResumableSearchRunner.run_chain (CollectionRootSearch.search_lawful spec.expected)
    (fun valid => CollectionRootSearch.Receipt.presented_step spec.expected valid)
    (CanonicalBags.canon source) ticks quantum

/-- One theorem connects actual emitted graph execution, source soundness
and complete successor coverage when the explored graph is settled. It
preserves the full native receipt list, even for repeated target values. -/
theorem root_emitted_graph_contract {name : String}
    (fresh : namesFresh spec name (.rootCollection certificate closed canonical) = true)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted (GeneralPlanEnvironment.environment spec.plan).language
      spec.plan.snapshot.free [] spec.expected source) (work : Nat) :
    let final := Complete.Settled.roundsUntilSettled (rootSearch certificate) work
      (Complete.Explore.begin (rootSearch certificate) (CanonicalBags.canon source))
    PureReturns (emittedRuntime spec name (.rootCollection certificate closed canonical)) [] state
      (apply (edgesHead name) [patternValue source, number work]) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm CompleteExecution.RootCollection.receiptTerm)
        (Complete.Graph.edges (rootSearch certificate) final))) ∧
    (∀ edge ∈ Complete.Graph.edges (rootSearch certificate) final,
      (Complete.Presented.gslt spec.plan [] spec.expected).Step edge.1 edge.2.2) ∧
    (Complete.Settled.settled (rootSearch certificate) final = true →
      ∀ node ∈ final.nodes, ∀ target,
        (Complete.Presented.gslt spec.plan [] spec.expected).Step node.state (CanonicalBags.canon target) ↔
          ∃ receipt, (node.state, receipt, CanonicalBags.canon target) ∈
            Complete.Graph.edges (rootSearch certificate) final) := by
  dsimp only
  refine ⟨root_edges_entry_returns certificate closed canonical footprinted fresh state source typed work, ?_, ?_⟩
  · obtain ⟨spent, _, reached⟩ := Complete.Graph.roundsUntilSettled_explore
      (S := rootSearch certificate) (CanonicalBags.canon source) work 0
    simp only [Nat.zero_add] at reached
    change Complete.Settled.roundsUntilSettled (rootSearch certificate) work
      (Complete.Explore.begin (rootSearch certificate) (CanonicalBags.canon source)) =
      Complete.Explore.explore (rootSearch certificate) (CanonicalBags.canon source) spent at reached
    intro edge member
    rw [reached] at member
    obtain ⟨valid, targetEq⟩ := Complete.Graph.edge_valid
      (CollectionRootSearch.search_lawful spec.expected) (CanonicalBags.canon source) spent edge member
    rw [targetEq]
    exact CollectionRootSearch.Receipt.presented_step spec.expected valid
  · intro done
    obtain ⟨spent, _, reached⟩ := Complete.Graph.roundsUntilSettled_explore
      (S := rootSearch certificate) (CanonicalBags.canon source) work 0
    simp only [Nat.zero_add] at reached
    change Complete.Settled.roundsUntilSettled (rootSearch certificate) work
      (Complete.Explore.begin (rootSearch certificate) (CanonicalBags.canon source)) =
      Complete.Explore.explore (rootSearch certificate) (CanonicalBags.canon source) spent at reached
    rw [reached] at done ⊢
    exact (CollectionRootSearch.settled_graph_source_exact certificate spec.expected source spent done).2

abbrev compiledRootSpec (snapshot : GeneralExecutionAdmission.Snapshot)
    (permissions : GeneralExecutionAdmission.Permissions) (expected : TypeExpr) : Spec :=
  ⟨GeneralExecutionAdmission.compile snapshot permissions, [], expected, .canonical⟩

omit footprinted

/-- The complete admission-to-execution statement for a recognized compiled
root profile. Native readiness is derived from compiled admission; neither
readiness nor source successor coverage is supplied as an extra certificate. -/
theorem emitted_root_compiled_graph
    {snapshot : GeneralExecutionAdmission.Snapshot} {permissions : GeneralExecutionAdmission.Permissions}
    (certificate : CollectionRootSearch.CoverageProfile (GeneralExecutionAdmission.compile snapshot permissions))
    (recognized : CollectionRootSearch.coverageProfile? (GeneralExecutionAdmission.compile snapshot permissions) =
      some certificate) (expected : TypeExpr) {name : String} {emitted : SpaceSemantics.Program}
    (accepted : emit? (compiledRootSpec snapshot permissions expected) name
      (admittedProfile (compiledRootSpec snapshot permissions expected)) = .ok emitted)
    (state : Effects.State) (source : Pattern)
    (typed : OpenPatternWellSorted
      (GeneralPlanEnvironment.environment (GeneralExecutionAdmission.compile snapshot permissions)).language
      snapshot.free [] expected source) (work : Nat) :
    let search := rootSearch (spec := compiledRootSpec snapshot permissions expected) certificate
    let final := Complete.Settled.roundsUntilSettled search work
      (Complete.Explore.begin search (CanonicalBags.canon source))
    PureReturns (runtime.append emitted) [] state
      (apply (edgesHead name) [patternValue source, number work]) state
      (encoded (encodeList (CompleteExecution.SearchWire.edgeTerm CompleteExecution.RootCollection.receiptTerm)
        (Complete.Graph.edges search final))) ∧
    (∀ edge ∈ Complete.Graph.edges search final,
      (Complete.Presented.gslt (GeneralExecutionAdmission.compile snapshot permissions) [] expected).Step edge.1 edge.2.2) ∧
    (Complete.Settled.settled search final = true →
      ∀ node ∈ final.nodes, ∀ target,
        (Complete.Presented.gslt (GeneralExecutionAdmission.compile snapshot permissions) [] expected).Step
          node.state (CanonicalBags.canon target) ↔
          ∃ receipt, (node.state, receipt, CanonicalBags.canon target) ∈ Complete.Graph.edges search final) := by
  have chosen := admittedProfile_root (spec := compiledRootSpec snapshot permissions expected)
    certificate rfl rfl recognized
  rw [chosen] at accepted
  obtain ⟨rfl, admitted⟩ := emit?_ok accepted
  exact root_emitted_graph_contract certificate rfl rfl
    (footprinted_of_root_compiled certificate [] expected .canonical) admitted.fresh state source typed work

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
