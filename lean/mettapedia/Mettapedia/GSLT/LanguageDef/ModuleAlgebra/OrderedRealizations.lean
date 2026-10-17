import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OrderedFirstOrderAdmission
import Mettapedia.GSLT.LanguageDef.OrderedMatchMachineAdequacy
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralProgramResumptionExecution
import Mathlib.Data.Multiset.ZeroCons

/-!
# Module realizations and their occurrence observations

The recorded source interpreter enumerates the authored rules and provider
queries independently of either executor. Compiled emissions retain its
initial and final bindings, query arguments and selected row positions. This
module joins that observation to the optimized module artifact and its actual
retained machine frontier. The source reader and native implementation remain
separate qualification boundaries.

Cross-machine semantics forget enumeration order while retaining complete
occurrences, multiplicity, bindings and provenance. The stronger list laws
below qualify the workers' common selected traversal policy. Each worker's
captured publication and residual execution remain ordered internally; this
does not impose a global MeTTa answer order or require every strategy's
bounded selection to choose the same occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OrderedRealizations

open Mettapedia.OSLF.MeTTaIL
open Syntax Match
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
open MeTTaILFirstOrderRuleCompilation
open WellSorted
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open GeneralProgramResumptionExecution
open Mettapedia.Machines Mettapedia.Machines.ExecutionHistoryReadout

/-- The compiled query observation of an independently recorded source event.
Provider positions are relation-local and precede successful-match filtering. -/
def queryChoice (query : RecordedQueryStep) : QueryRowChoice :=
  ⟨query.relation, query.instantiated, .provider,
    query.event.tuplePosition, query.event.tuple⟩

def premiseReadout (run : RecordedPremiseRun) : PremiseReceipt :=
  ⟨run.bindings, run.queries.map queryChoice⟩

def rootReadout (ordinal : Nat) (run : RecordedRootRun) : RuleEmission Nat :=
  ⟨ordinal, run.initial, run.completed.bindings,
    run.completed.queries.map queryChoice, run.target⟩

def occurrenceReadout (run : RecordedRuleRun) : RuleEmission Nat :=
  rootReadout run.ordinal run.run

/-- Each compiled query and continuation agrees with the original premise
syntax and its recorded provider events, including equal tuple occurrences. -/
theorem premise_receipts_recorded (relations : Engine.RelationEnv)
    (language : LanguageDef) (plans : List PremisePlan)
    (explicit : ∀ plan ∈ plans, plan.relation ≠ "eq")
    (position : Nat) (initial : Bindings) :
    runPremiseReceipts relations language plans initial =
      (recordedPremiseRuns relations language (erasePremisePlans plans)
        position initial).map premiseReadout := by
  induction plans generalizing position initial with
  | nil => rfl
  | cons plan plans ih =>
    simp only [runPremiseReceipts, erasePremisePlans, List.map_cons,
      PremisePlan.erase, recordedPremiseRuns, List.map_flatMap]
    rw [plan.runReceipts_eq_recordedEvents_of_not_eq relations language initial
      (explicit plan (by simp)), List.flatMap_map]
    apply List.flatMap_congr
    intro event _
    rw [ih (fun later member => explicit later (by simp [member]))]
    simp only [PremisePlan.receiptOfRecordedEvent, List.map_map]
    rfl

/-- The residual matcher, query operations and instantiator reproduce the
full original rule occurrence, rather than just its resulting term. -/
theorem rule_emissions_recorded (relations : Engine.RelationEnv)
    (language : LanguageDef) (plan : RulePlan)
    (explicit : ∀ query ∈ plan.premises, query.relation ≠ "eq")
    (ordinal : Nat) (subject : Pattern) :
    plan.runEmissions relations language ordinal subject =
      (recordedRootRuns relations language plan.erase subject).map
        (rootReadout ordinal) := by
  simp only [RulePlan.runEmissions, recordedRootRuns, RulePlan.erase,
    run_eq_matchPattern, List.map_flatMap]
  apply List.flatMap_congr
  intro initial _
  rw [premise_receipts_recorded relations language plan.premises explicit 0 initial,
    List.map_map]
  simp only [instantiate_eq_applyBindings, List.map_map]
  rfl

private theorem zipIdx_finRange {α : Type} (items : List α) :
    items.zipIdx = (List.finRange items.length).map fun index => (items[index], index.val) := by
  apply List.ext_getElem (by simp)
  intro index left right
  simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_finRange, Nat.zero_add]
  rfl

/-- The independently authored rule order is the compiled occurrence order.
The supplied premise restriction is local syntax, not an assumed run law. -/
theorem program_emissions_recorded (relations : Engine.RelationEnv)
    (language : LanguageDef) (program : RuleProgram language.rewrites)
    (explicit : ∀ occurrence, ∀ query ∈ (program.planAt occurrence).premises,
      query.relation ≠ "eq") (subject : Pattern) :
    (List.finRange language.rewrites.length).flatMap
        (fun occurrence => (program.planAt occurrence).runEmissions
          relations language occurrence.val subject) =
      (recordedRootOccurrences relations language subject).map occurrenceReadout := by
  simp only [recordedRootOccurrences, zipIdx_finRange, List.flatMap_map, List.map_flatMap,
    List.map_map]
  apply List.flatMap_congr
  intro occurrence _
  rw [rule_emissions_recorded relations language (program.planAt occurrence)
    (explicit occurrence) occurrence.val subject, program.erase_planAt]
  rfl

/-- Invocation selection filters candidates at their original ordinals. It
does not renumber the successful rules or the occurrences they produce. -/
theorem guarded_program_emissions_recorded (relations : Engine.RelationEnv)
    (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (program : RuleProgram language.rewrites)
    (explicit : ∀ occurrence, ∀ query ∈ (program.planAt occurrence).premises,
      query.relation ≠ "eq") (type : TypeExpr) (subject : Pattern) :
    (List.finRange language.rewrites.length).flatMap
        (fun occurrence => if rootInvocationGuard language provider type occurrence.val then
          (program.planAt occurrence).runEmissions relations language occurrence.val subject else []) =
      (recordedGuardedRootOccurrences relations language provider type subject).map occurrenceReadout := by
  simp only [recordedGuardedRootOccurrences, zipIdx_finRange, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro occurrence _
  cases rootInvocationGuard language provider type occurrence.val with
  | false => simp only [Bool.false_eq_true, ↓reduceIte, List.map_nil]
  | true =>
    simp only [↓reduceIte, List.map_map]
    rw [rule_emissions_recorded relations language (program.planAt occurrence)
      (explicit occurrence) occurrence.val subject, program.erase_planAt]
    rfl

/-- The common occurrence observation retains the original source witness
and its agreement with the actual scoped stores and provider event history. -/
def SameOccurrence (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (raw : RootReadout) (emission : RuleEmission Nat) : Prop :=
  ∃ recorded, RuleRunAgreement language provider raw recorded ∧
    occurrenceReadout recorded = emission

theorem SameOccurrence.ordinal {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} {raw : RootReadout}
    {emission : RuleEmission Nat} (same : SameOccurrence language provider raw emission) :
    raw.ordinal = emission.origin := by
  obtain ⟨recorded, ⟨rule, _, agreement⟩, rfl⟩ := same
  exact agreement.ordinal

theorem SameOccurrence.target {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} {raw : RootReadout}
    {emission : RuleEmission Nat} (same : SameOccurrence language provider raw emission) :
    raw.target = emission.target := by
  obtain ⟨recorded, ⟨rule, _, agreement⟩, rfl⟩ := same
  exact agreement.target

/-- Portable declaration origins are selected by the original rule ordinal,
never by the position of an answer after failed candidates were removed. -/
theorem SameOccurrence.portable_origin {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot} {raw : RootReadout}
    {emission : RuleEmission Nat} (same : SameOccurrence source.core provider raw emission) :
    source.originAt? raw.ordinal = source.originAt? emission.origin := by
  rw [same.ordinal]

/-- The transported origin is an actual declaration entry on both sides;
agreement cannot be obtained from two failed lookups. -/
theorem SameOccurrence.origin_exists {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {raw : RootReadout} {emission : RuleEmission Nat}
    (same : SameOccurrence source.core provider raw emission) :
    ∃ origin, source.originAt? raw.ordinal = some origin ∧
      source.originAt? emission.origin = some origin := by
  have inExecuted : emission.origin < (environment source.core provider).language.rewrites.length := by
    obtain ⟨recorded, ⟨rule, declared, _⟩, rfl⟩ := same
    exact (List.getElem?_eq_some_iff.mp declared).1
  have lengths := congrArg List.length admitted.profile.firstOrder.sameRules
  simp only [List.length_map] at lengths
  have inSource : emission.origin < source.order.length := by
    rw [lengths, admitted.rows_eq, OrderedFirstOrderAdmission.Source.ruleRows, List.length_map]
      at inExecuted
    exact inExecuted
  have found : source.originAt? emission.origin = some source.order[emission.origin].origin := by
    simp [OrderedFirstOrderAdmission.Source.originAt?, List.getElem?_eq_getElem inSource]
  exact ⟨_, same.portable_origin.trans found, found⟩

/-- The actual authored completed job receipts have the independent guarded
source observation, including their logical bindings and selected query rows. -/
theorem authored_recorded_observation {language : LanguageDef}
    {provider : GeneralPremise.ProviderSnapshot} (facts : QueryProfileFacts language provider)
    {bound : List TypeExpr} {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free bound type subject) :
    List.Forall₂ (SameOccurrence language provider)
      ((GeneralRuleJobExecution.completedReceipts (rootPlan language provider) bound type subject).map
        receiptReadout)
      ((recordedGuardedRootOccurrences (providerRelEnv provider) language provider type subject).map
        occurrenceReadout) := by
  rw [List.forall₂_map_right_iff]
  exact (completedReceipts_guarded_recorded_occurrences facts shape typed).imp
    (fun raw recorded related => ⟨recorded, related, rfl⟩)

/-- The actual fused instruction tree selected by the admitted module. -/
def rawMachineProgram {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) : OrderedMatchMachineLanguage.Program :=
  OrderedMatchMachineLanguage.mapProgram Fin.val OrderedMatchMachineLanguage.toMachinePlan
    admitted.fusedProgram

/-- At any suspension, the actual emitted prefix and retained frontier still
denote the complete independently recorded source occurrence stream. -/
theorem raw_fused_suspension_recorded {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (explicit : ∀ occurrence, ∀ query ∈ (admitted.program.planAt occurrence).premises,
      query.relation ≠ "eq") (subject : Pattern) (fuel : Nat) :
    (recordedRootOccurrences (providerRelEnv provider) source.core subject).map occurrenceReadout =
      (OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core fuel
        (OrderedMatchMachineLanguage.startFrontier (rawMachineProgram admitted) subject)).emissions ++
      OrderedMatchMachineLanguage.frontierEmissions (providerRelEnv provider) source.core
        (OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core fuel
          (OrderedMatchMachineLanguage.startFrontier (rawMachineProgram admitted) subject)).pending := by
  rw [← program_emissions_recorded (providerRelEnv provider) source.core admitted.program
    explicit subject, ← admitted.fusedProgram_emissions (providerRelEnv provider) subject,
    ← OrderedMatchMachineLanguage.frontierEmissions_mapProgram (providerRelEnv provider)
      source.core admitted.fusedProgram Fin.val subject]
  exact OrderedMatchMachineLanguage.runFrontier_observation _ _ _ _

/-- Checked invocation-sort selection happens before the fused machine starts;
the instruction leaves still carry the original declaration indices. -/
def machineProgram {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr) :
    OrderedMatchMachineLanguage.Program :=
  OrderedMatchMachineLanguage.mapProgram Fin.val OrderedMatchMachineLanguage.toMachinePlan
    (admitted.sortedFusedProgram type)

theorem fused_frontier_recorded {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (type : TypeExpr) (subject : Pattern) :
    OrderedMatchMachineLanguage.frontierEmissions (providerRelEnv provider) source.core
        (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject) =
      (recordedGuardedRootOccurrences (providerRelEnv provider) source.core provider type subject).map
        occurrenceReadout := by
  unfold machineProgram
  rw [OrderedMatchMachineLanguage.frontierEmissions_mapProgram,
    admitted.sortedFusedProgram_emissions]
  exact guarded_program_emissions_recorded _ _ _ _ admitted.explicit_queries _ _

/-- Every actual fused suspension partitions the independent ordered source
stream into emitted occurrences and the meaning of the retained instructions. -/
theorem fused_suspension_recorded {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (type : TypeExpr) (subject : Pattern) (fuel : Nat) :
    (recordedGuardedRootOccurrences (providerRelEnv provider) source.core provider type subject).map
        occurrenceReadout =
      (OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core fuel
        (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject)).emissions ++
      OrderedMatchMachineLanguage.frontierEmissions (providerRelEnv provider) source.core
        (OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core fuel
          (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject)).pending := by
  rw [← fused_frontier_recorded admitted type subject]
  exact OrderedMatchMachineLanguage.runFrontier_observation _ _ _ _

/-- Complete authored receipts and the actual drained fused execution carry
the same ordered occurrences. The relation retains the scoped stores and
their exact logical binding/provenance agreement, including duplicates. -/
theorem completed_realizations {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {bound : List TypeExpr} {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free bound type subject) (fuel : Nat)
    (enough : OrderedMatchMachineLanguage.frontierWork (providerRelEnv provider) source.core
      (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject) ≤ fuel) :
    List.Forall₂ (SameOccurrence source.core provider)
      ((GeneralRuleJobExecution.completedReceipts (rootPlan source.core provider) bound type subject).map
        receiptReadout)
      (OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core fuel
        (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject)).emissions := by
  rw [OrderedMatchMachineLanguage.runFrontier_emissions_of_completed _ _ _ _ enough,
    fused_frontier_recorded]
  exact authored_recorded_observation admitted.profile shape typed

/-- A completed fused firing inherits its actual authored receipt's typing
evidence. This is earned from the occurrence correspondence, not an extra
typing assertion supplied to the compiled evaluator. -/
theorem completed_fused_target_typed {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {bound : List TypeExpr} {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free bound type subject) (fuel : Nat)
    (enough : OrderedMatchMachineLanguage.frontierWork (providerRelEnv provider) source.core
      (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject) ≤ fuel)
    {emission : RuleEmission Nat}
    (member : emission ∈ (OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider)
      source.core fuel (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type)
        subject)).emissions) :
    OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free bound type emission.target := by
  obtain ⟨raw, present, same⟩ := Mettapedia.GSLT.Distinction.forall₂_right_mem
    (completed_realizations admitted shape typed fuel enough) member
  obtain ⟨receipt, receiptMember, rfl⟩ := List.mem_map.mp present
  have valid := GeneralRuleJobExecution.completedReceipts_valid receiptMember
  rw [← same.target]
  exact valid.2.2.2.2

/-- The module's original licensed requests, advanced by the authored driver.
Only its per-job work allocation varies; no answer list is an input. -/
def authoredProgram {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (_admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (bound : List TypeExpr) (type : TypeExpr) (subject : Pattern)
    (budget : GeneralRuleJobs.Job → Nat) : ProgramRun :=
  ProgramRun.ofInvocations (GeneralProgramDriverExecution.invocations
    (rootPlan source.core provider) bound type subject budget)

theorem authored_publication_recorded {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {bound : List TypeExpr} {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free bound type subject)
    (budget : GeneralRuleJobs.Job → Nat) :
    let program := authoredProgram admitted bound type subject budget
    List.Forall₂ (SameOccurrence source.core provider)
      (program.publication.map receiptReadout)
      (((recordedGuardedRootOccurrences (providerRelEnv provider) source.core provider type subject).map
        occurrenceReadout).take program.publication.length) := by
  dsimp only [authoredProgram]
  rw [← List.map_take, List.forall₂_map_right_iff]
  exact (ProgramRun.root_publication_guarded_prefix admitted.profile shape typed budget).imp
    (fun raw recorded related => ⟨recorded, related, rfl⟩)

theorem authored_conservation_recorded {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {bound : List TypeExpr} {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free bound type subject)
    (budget : GeneralRuleJobs.Job → Nat) :
    let program := authoredProgram admitted bound type subject budget
    List.Forall₂ (SameOccurrence source.core provider)
      ((program.publication ++ program.withheld).map receiptReadout)
      ((recordedGuardedRootOccurrences (providerRelEnv provider) source.core provider type subject).map
        occurrenceReadout) := by
  dsimp only [authoredProgram]
  rw [List.forall₂_map_right_iff]
  exact (ProgramRun.root_publication_guarded_conservation admitted.profile shape typed budget).imp
    (fun raw recorded related => ⟨recorded, related, rfl⟩)

/-- At arbitrary work cuts, both actual retained realizations still carry
the same complete source stream. Publication and remaining work are kept
separate, so a singleton prefix gives no completion or pruning permission. -/
theorem retained_realizations {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {bound : List TypeExpr} {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free bound type subject)
    (budget : GeneralRuleJobs.Job → Nat) (fuel : Nat) :
    let authored := authoredProgram admitted bound type subject budget
    let fused := OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core fuel
      (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject)
    List.Forall₂ (SameOccurrence source.core provider)
      ((authored.publication ++ authored.withheld).map receiptReadout)
      (fused.emissions ++ OrderedMatchMachineLanguage.frontierEmissions (providerRelEnv provider)
        source.core fused.pending) := by
  dsimp only
  rw [← fused_suspension_recorded admitted type subject fuel]
  exact authored_conservation_recorded admitted shape typed budget

/-- Closed firings stay inside the admitted first-order carrier. Typed
provider data alone would not establish this: its representation is checked
by module admission, and scope zero excludes rigid bound indices. -/
theorem completed_fused_target_firstOrder {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) (fuel : Nat)
    (enough : OrderedMatchMachineLanguage.frontierWork (providerRelEnv provider) source.core
      (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject) ≤ fuel)
    {emission : RuleEmission Nat}
    (member : emission ∈ (OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider)
      source.core fuel (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type)
        subject)).emissions) :
    GeneralFirstOrderProjection.FirstOrder emission.target := by
  have targetTyped := completed_fused_target_typed admitted shape typed fuel enough member
  apply admitted.sortedFusedProgram_target_firstOrder_of_scope_zero type subject
    shape.isMatchCorrect emission
  · rw [← OrderedMatchMachineLanguage.runFrontier_mapProgram_completed
      (providerRelEnv provider) source.core (admitted.sortedFusedProgram type) Fin.val subject fuel enough]
    exact member
  · exact targetTyped.2.2.2

/-- The authored machine's computable local expansion bound. It counts the
actual tree for the selected job, including rejected attempts. -/
def authoredBudget {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (_admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (job : GeneralRuleJobs.Job) : Nat :=
  (GeneralPremise.Execution.treeStart (environment source.core provider)
    (.root job.site.focusBound job.site.focusType job.site.focus job.ordinal)).cost

/-- A boundary drain executes the original fused instructions. Its fuel is
their proved work bound, rather than a bound on the number of source firings. -/
def fusedDrain {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (type : TypeExpr) (subject : Pattern) : OrderedMatchMachineLanguage.OrderedCut :=
  let pending := OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject
  OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core
    (OrderedMatchMachineLanguage.frontierWork (providerRelEnv provider) source.core pending) pending

/-- The shared block law settles the actual candidate instructions into one
valid terminal per independent source firing. The entry invariant is earned
from the compiled program, including when there are zero or duplicate results.
This is local enumeration; subsequent language firings use the boundary runner. -/
theorem fused_settled_occurrences {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (type : TypeExpr) (subject : Pattern) :
    List.Forall₂ (fun emission settled => settled.val.emission? = some emission)
      ((recordedGuardedRootOccurrences (providerRelEnv provider) source.core provider type subject).map
        occurrenceReadout)
      ((OrderedMatchMachineLanguage.localTarget (providerRelEnv provider) source.core).settle
        OrderedMatchMachineLanguage.localStable
        (OrderedMatchMachineLanguage.machineRank
          (.run (machineProgram admitted type) subject [subject]) + 1)
        (OrderedMatchMachineLanguage.localStart (machineProgram admitted type) subject)) := by
  rw [← fused_frontier_recorded admitted type subject,
    OrderedMatchMachineLanguage.frontierEmissions_start]
  exact OrderedMatchMachineLanguage.settle_start_receipts _ _ _ _

/-- The real depth-first drain and ranked block settlement use different
clocks but expose exactly the same full firing occurrences. -/
theorem fused_drain_settled {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (type : TypeExpr) (subject : Pattern) :
    List.Forall₂ (fun emission settled => settled.val.emission? = some emission)
      (fusedDrain admitted type subject).emissions
      ((OrderedMatchMachineLanguage.localTarget (providerRelEnv provider) source.core).settle
        OrderedMatchMachineLanguage.localStable
        (OrderedMatchMachineLanguage.machineRank
          (.run (machineProgram admitted type) subject [subject]) + 1)
        (OrderedMatchMachineLanguage.localStart (machineProgram admitted type) subject)) := by
  have drained : (fusedDrain admitted type subject).emissions =
      (recordedGuardedRootOccurrences (providerRelEnv provider) source.core provider type subject).map
        occurrenceReadout := by
    unfold fusedDrain
    rw [OrderedMatchMachineLanguage.runFrontier_emissions_of_completed _ _ _ _ (Nat.le_refl _)]
    exact fused_frontier_recorded admitted type subject
  rw [drained]
  exact fused_settled_occurrences admitted type subject

/-- A noncommitting task preserves the actual job's receipt history. Its
configuration still retains unresolved obligations. This does not classify a
program-level publication release as administrative. -/
theorem authored_job_tick_silent (job : JobRun)
    (noncommitting : ∀ task ∈ job.state.agenda.head?, task.commits = false) :
    (job.resume 1).receipts = job.receipts := by
  have silent := GeneralPremise.Execution.tick_answers_of_noncommitting
    job.request.val.environment job.request.val.goal job.state noncommitting
  change (((GeneralPremise.Execution.tick job.request.val.environment job.request.val.goal
    job.state).answers.filterMap
      (GeneralRuleJobExecution.rootProjection job.request.val job.request.property)).map
        Subtype.val) = _
  rw [silent]
  rfl

/-- Static premise completeness is derived from the module's actual compiled
syntax and the checked common profile. It is not a run oracle in admission. -/
theorem static_admission {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) :
    GeneralPremise.Static.checkLanguage (environment source.core provider) = true := by
  apply admitted.profile.static_of_queries
  intro index rule declared premise member
  obtain ⟨authored, selected, sameCore⟩ := admitted.profile.firstOrder.authored declared
  have samePremises := congrArg (fun core : Pattern × Pattern × List Premise => core.2.2) sameCore
  change authored.premises = rule.premises at samePremises
  rw [← samePremises] at member
  obtain ⟨inBounds, same⟩ := List.getElem?_eq_some_iff.mp selected
  let occurrence : Fin source.core.rewrites.length := ⟨index, inBounds⟩
  have erased : (admitted.program.planAt occurrence).erase = authored :=
    (admitted.program.erase_planAt occurrence).trans same
  rw [← erased] at member
  change premise ∈ (admitted.program.planAt occurrence).premises.map PremisePlan.erase at member
  obtain ⟨query, _, rfl⟩ := List.mem_map.mp member
  exact ⟨query.relation, erasePatterns query.arguments, rfl⟩

/-- The existing authored retained program run at its earned local bounds. -/
def authoredDrain {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    (type : TypeExpr) (subject : Pattern) : ProgramRun :=
  authoredProgram admitted [] type subject (authoredBudget admitted)

theorem authoredDrain_publication {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) :
    (authoredDrain admitted type subject).publication =
      GeneralRuleJobExecution.completedReceipts (rootPlan source.core provider) [] type subject := by
  exact ProgramRun.publication_eq_completed_of_static (rootPlan source.core provider) [] type subject
    (static_admission admitted) typed.2.1 (authoredBudget admitted) (fun _ _ => Nat.le_refl _)

theorem drained_realizations {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) :
    List.Forall₂ (SameOccurrence source.core provider)
      ((authoredDrain admitted type subject).publication.map receiptReadout)
      (fusedDrain admitted type subject).emissions := by
  rw [authoredDrain_publication admitted typed]
  exact completed_realizations admitted shape typed _ (Nat.le_refl _)

/-- Bounded delivery reads the same occurrence slice on both sides. The
offset names already delivered occurrences, so repeated equal values do not
reset the cursor. Limit zero and first-success delivery are instances. -/
theorem bounded_occurrences {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) (offset limit : Nat) :
    List.Forall₂ (SameOccurrence source.core provider)
      ((((authoredDrain admitted type subject).publication.drop offset).take limit).map receiptReadout)
      (((fusedDrain admitted type subject).emissions.drop offset).take limit) ∧
    List.Forall₂ (SameOccurrence source.core provider)
      (((authoredDrain admitted type subject).publication.drop (offset + limit)).map receiptReadout)
      ((fusedDrain admitted type subject).emissions.drop (offset + limit)) := by
  have paired := drained_realizations admitted shape typed
  constructor
  · simpa only [List.map_take, List.map_drop] using
      List.forall₂_take limit (List.forall₂_drop offset paired)
  · simpa only [List.map_drop] using List.forall₂_drop (offset + limit) paired

/-- Actual bounded cursor advancement preserves the common occurrence
observation, its absolute delivery positions and the retained captured prefix.
Compatibility is checked separately for each representation. These pure
cursor laws do not supply authority to copy or replay an earlier cursor. -/
theorem bounded_delivery {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject)
    {StreamId : Type} [DecidableEq StreamId] [DecidableEq (RuleEmission Nat)]
    (producer : Nat) (lineage : StoreReadToken StreamId Nat)
    (authoredCursor : Publication.Cursor StreamId GeneralRuleJobs.Receipt)
    (fusedCursor : Publication.Cursor StreamId (RuleEmission Nat)) (limit : Nat)
    (authoredCompatible : Publication.Compatible authoredCursor
      ⟨lineage.storeId, lineage.revision, (authoredDrain admitted type subject).publication⟩)
    (fusedCompatible : Publication.Compatible fusedCursor
      ⟨lineage.storeId, lineage.revision, (fusedDrain admitted type subject).emissions⟩)
    (offsets : authoredCursor.next = fusedCursor.next)
    (captured : List.Forall₂ (SameOccurrence source.core provider)
      (authoredCursor.captured.entries.map receiptReadout) fusedCursor.captured.entries) :
    let authored := Delivery.bounded producer lineage authoredCursor
      (authoredDrain admitted type subject) 0 limit
    let fused := Publication.advanceBounded producer fusedCursor
      ⟨lineage.storeId, lineage.revision, (fusedDrain admitted type subject).emissions⟩ limit
    ∃ receipts emissions,
      List.Forall₂ (SameOccurrence source.core provider) (receipts.map receiptReadout) emissions ∧
      authored.2 = some (answerEvents authoredCursor.next producer receipts) ∧
      fused.2 = some (answerEvents authoredCursor.next producer emissions) ∧
      authored.1.next = fused.1.next ∧
      authored.1.captured.readToken = fused.1.captured.readToken ∧
      List.Forall₂ (SameOccurrence source.core provider)
        (authored.1.captured.entries.map receiptReadout) fused.1.captured.entries := by
  have paired := (bounded_occurrences admitted shape typed authoredCursor.next limit).1
  have first := Publication.advanceBounded_accepted producer authoredCursor
    ⟨lineage.storeId, lineage.revision, (authoredDrain admitted type subject).publication⟩
    limit authoredCompatible
  have second := Publication.advanceBounded_accepted producer fusedCursor
    ⟨lineage.storeId, lineage.revision, (fusedDrain admitted type subject).emissions⟩
    limit fusedCompatible
  dsimp only [Delivery.bounded]
  rw [ProgramRun.resume_zero, first, second]
  dsimp only
  rw [← offsets]
  refine ⟨_, _, paired, rfl, rfl, ?_, ?_, ?_⟩
  · have lengths := paired.length_eq
    simp only [List.length_map] at lengths
    exact congrArg (authoredCursor.next + ·) lengths
  · exact authoredCompatible.2.1.trans fusedCompatible.2.1.symm
  · rw [List.map_append]
    exact List.rel_append captured paired

theorem authoredDrain_target_typed {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject)
    {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (authoredDrain admitted type subject).publication) :
    OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type receipt.target := by
  rw [authoredDrain_publication admitted typed] at member
  exact (GeneralRuleJobExecution.completedReceipts_valid member).2.2.2.2

theorem authoredDrain_target_firstOrder {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject)
    {receipt : GeneralRuleJobs.Receipt}
    (member : receipt ∈ (authoredDrain admitted type subject).publication) :
    GeneralFirstOrderProjection.FirstOrder receipt.target := by
  have paired := List.forall₂_map_left_iff.mp (drained_realizations admitted shape typed)
  obtain ⟨emission, present, same⟩ := Mettapedia.GSLT.Distinction.forall₂_right_mem
    (Mettapedia.GSLT.Distinction.OrderedSimulation.forall₂_swap paired) member
  have targetShape := completed_fused_target_firstOrder admitted shape typed _ (Nat.le_refl _) present
  rw [← same.target] at targetShape
  exact targetShape

/-- At a source boundary the term stays in the checked carrier, while its
entire occurrence history survives. The two executors keep their own event
representations rather than quotienting histories by target equality. -/
structure Boundary (language : LanguageDef) (provider : GeneralPremise.ProviderSnapshot)
    (type : TypeExpr) (Event : Type) where
  subject : Pattern
  shape : GeneralFirstOrderProjection.FirstOrder subject
  typed : OpenPatternWellSorted (environment language provider).language
    (environment language provider).free [] type subject
  history : List Event

def Boundary.start {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}
    {type : TypeExpr} {subject : Pattern} (Event : Type)
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment language provider).language
      (environment language provider).free [] type subject) : Boundary language provider type Event :=
  ⟨subject, shape, typed, []⟩

def SameBoundary {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}
    {type : TypeExpr} (authored : Boundary language provider type RootReadout)
    (fused : Boundary language provider type (RuleEmission Nat)) : Prop :=
  authored.subject = fused.subject ∧
    List.Forall₂ (SameOccurrence language provider) authored.history fused.history

def authoredStep {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr)
    (state : Boundary source.core provider type RootReadout) :
    List (Boundary source.core provider type RootReadout) :=
  (authoredDrain admitted type state.subject).publication.attach.map fun receipt =>
    ⟨receipt.val.target,
      authoredDrain_target_firstOrder admitted state.shape state.typed receipt.property,
      authoredDrain_target_typed admitted state.typed receipt.property,
      state.history ++ [receiptReadout receipt.val]⟩

def fusedStep {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr)
    (state : Boundary source.core provider type (RuleEmission Nat)) :
    List (Boundary source.core provider type (RuleEmission Nat)) :=
  (fusedDrain admitted type state.subject).emissions.attach.map fun emission =>
    ⟨emission.val.target,
      completed_fused_target_firstOrder admitted state.shape state.typed _ (Nat.le_refl _) emission.property,
      completed_fused_target_typed admitted state.shape state.typed _ (Nat.le_refl _) emission.property,
      state.history ++ [emission.val]⟩

/-- Even a firing that returns its input adds a physical history occurrence;
retaining only the target would lose this progress distinction. -/
theorem authoredStep_history_length {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr)
    {before after : Boundary source.core provider type RootReadout}
    (member : after ∈ authoredStep admitted type before) :
    after.history.length = before.history.length + 1 := by
  obtain ⟨receipt, _, rfl⟩ := List.mem_map.mp member
  simp only [List.length_append, List.length_singleton]

theorem fusedStep_history_length {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr)
    {before after : Boundary source.core provider type (RuleEmission Nat)}
    (member : after ∈ fusedStep admitted type before) :
    after.history.length = before.history.length + 1 := by
  obtain ⟨emission, _, rfl⟩ := List.mem_map.mp member
  simp only [List.length_append, List.length_singleton]

/-- A source macro-step drains original authored jobs. An empty completed
firing is terminal; a self-loop remains a successor with a longer history. -/
def authoredSystem {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr) :
    Mettapedia.GSLT.Distinction.OrderedSystem (Boundary source.core provider type RootReadout) where
  step := authoredStep admitted type
  halted state := (authoredDrain admitted type state.subject).publication.isEmpty

/-- The alternative macro-step runs the fused instruction frontier to its
local work bound. No global normalization or termination premise is used. -/
def fusedSystem {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr) :
    Mettapedia.GSLT.Distinction.OrderedSystem
      (Boundary source.core provider type (RuleEmission Nat)) where
  step := fusedStep admitted type
  halted state := (fusedDrain admitted type state.subject).emissions.isEmpty

/-- A worker may publish each completed local firing block in reverse order.
Local blocks are finite; this does not reverse an unfinished or infinite
execution, or alter the causal history carried by an individual occurrence. -/
def reversedFusedSystem {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr) :
    Mettapedia.GSLT.Distinction.OrderedSystem
      (Boundary source.core provider type (RuleEmission Nat)) where
  step state := (fusedStep admitted type state).reverse
  halted := (fusedSystem admitted type).halted

private theorem attach_related {α β : Type} {related : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ related left right) :
    List.Forall₂ (fun a b => related a.val b.val) left.attach right.attach := by
  have erased : List.Forall₂ related (left.attach.map Subtype.val)
      (right.attach.map Subtype.val) := by simpa using paired
  exact List.forall₂_map_right_iff.mp (List.forall₂_map_left_iff.mp erased)

private theorem related_isEmpty {α β : Type} {related : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ related left right) :
    right.isEmpty = left.isEmpty := by
  cases paired <;> rfl

/-- Local source correspondence and carrier closure earn a simulation of the
two actual boundary machines. Every ordered occurrence extends the matching
history on both sides, including duplicate-valued firings. -/
theorem boundary_simulation {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr) :
    Mettapedia.GSLT.Distinction.OrderedSimulation
      (authoredSystem admitted type) (fusedSystem admitted type) SameBoundary where
  halted := by
    rintro ⟨subject, shape, typed, history⟩ ⟨other, otherShape, otherTyped, otherHistory⟩ ⟨rfl, _⟩
    simpa only [authoredSystem, fusedSystem, List.isEmpty_map] using
      related_isEmpty (drained_realizations admitted shape typed)
  step := by
    rintro ⟨subject, shape, typed, history⟩ ⟨other, otherShape, otherTyped, otherHistory⟩
      ⟨rfl, histories⟩
    have paired := List.forall₂_map_left_iff.mp (drained_realizations admitted shape typed)
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    exact (attach_related paired).imp fun raw emission same =>
      ⟨same.target, List.rel_append histories (.cons same .nil)⟩

/-- The selected workers satisfy the general occurrence contract; their
stronger traversal agreement is a refinement of this observation. -/
theorem boundary_occurrence_simulation {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr) :
    Mettapedia.GSLT.Distinction.OccurrenceSimulation
      (authoredSystem admitted type) (fusedSystem admitted type) SameBoundary :=
  Mettapedia.GSLT.Distinction.OccurrenceSimulation.ofOrdered (boundary_simulation admitted type)

/-- Reordering complete local blocks preserves source occurrence histories,
bindings and origins. No positional pairing of successor lists is required. -/
theorem reversed_boundary_occurrence_simulation {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr) :
    Mettapedia.GSLT.Distinction.OccurrenceSimulation
      (authoredSystem admitted type) (reversedFusedSystem admitted type) SameBoundary where
  halted := (boundary_occurrence_simulation admitted type).halted
  step := by
    intro authored fused related
    simpa only [reversedFusedSystem, fusedSystem, Multiset.coe_reverse] using
      (boundary_occurrence_simulation admitted type).step related

/-- Every finite synchronous source-depth frontier has the same occurrence
bag under the alternative worker policy. Individual histories remain intact;
different depth-first cuts and first selections need not coincide. -/
theorem subject_reversed_frontier_bags {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) (count : Nat) :
    Multiset.Rel SameBoundary
      (((authoredSystem admitted type).runFrontier count [Boundary.start RootReadout shape typed]) :
        Multiset (Boundary source.core provider type RootReadout))
      (((reversedFusedSystem admitted type).runFrontier count
        [Boundary.start (RuleEmission Nat) shape typed]) :
        Multiset (Boundary source.core provider type (RuleEmission Nat))) :=
  (reversed_boundary_occurrence_simulation admitted type).runFrontier count
    (.cons ⟨rfl, .nil⟩ .zero)

/-- Every finite source-depth frontier agrees position by position, with its
full occurrence histories and still-running self-loops. The existing common
machine theorem supplies the induction; no second runner is introduced. -/
theorem finite_frontiers {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr)
    (count : Nat) {authored : List (Boundary source.core provider type RootReadout)}
    {fused : List (Boundary source.core provider type (RuleEmission Nat))}
    (paired : List.Forall₂ SameBoundary authored fused) :
    List.Forall₂ SameBoundary
      ((authoredSystem admitted type).runFrontier count authored)
      ((fusedSystem admitted type).runFrontier count fused) :=
  (boundary_simulation admitted type).runFrontier count paired

/-- The same correspondence covers every depth-first source prefix, including
unfinished alternatives, without assuming termination of the rewrite program. -/
theorem finite_depthFirst_prefixes {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider) (type : TypeExpr)
    (count : Nat) {authored : List (Boundary source.core provider type RootReadout)}
    {fused : List (Boundary source.core provider type (RuleEmission Nat))}
    (paired : List.Forall₂ SameBoundary authored fused) :
    List.Forall₂ SameBoundary
      (((authoredSystem admitted type).expandFirst)^[count] authored)
      (((fusedSystem admitted type).expandFirst)^[count] fused) :=
  (boundary_simulation admitted type).expandFirst_iterate count paired

/-- Starting with the admitted subject constructs the initial correspondence.
The theorem covers every finite source-depth run, including non-normalizing
programs, rather than requiring an initial simulation certificate as input. -/
theorem subject_frontiers {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) (count : Nat) :
    List.Forall₂ SameBoundary
      ((authoredSystem admitted type).runFrontier count [Boundary.start RootReadout shape typed])
      ((fusedSystem admitted type).runFrontier count [Boundary.start (RuleEmission Nat) shape typed]) :=
  finite_frontiers admitted type count (.cons ⟨rfl, .nil⟩ .nil)

theorem subject_depthFirst_prefixes {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) (count : Nat) :
    List.Forall₂ SameBoundary
      (((authoredSystem admitted type).expandFirst)^[count] [Boundary.start RootReadout shape typed])
      (((fusedSystem admitted type).expandFirst)^[count] [Boundary.start (RuleEmission Nat) shape typed]) :=
  finite_depthFirst_prefixes admitted type count (.cons ⟨rfl, .nil⟩ .nil)

/-- Complete cross-machine correspondence at the language-level observer:
occurrences are paired with multiplicity, bindings and provenance, without
requiring one common enumeration order. -/
theorem completed_occurrence_bags {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) :
    Multiset.Rel (SameOccurrence source.core provider)
      (((authoredDrain admitted type subject).publication.map receiptReadout) : Multiset RootReadout)
      ((fusedDrain admitted type subject).emissions : Multiset (RuleEmission Nat)) :=
  Mettapedia.GSLT.Distinction.OccurrenceSimulation.forall₂_multisetRel
    (drained_realizations admitted shape typed)

/-- Any permutation of a completed worker's full occurrence records has the
same public meaning. This does not license altering a captured cursor prefix
or moving committed effects across their dependencies. -/
theorem completed_occurrence_bags_of_permutation {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject)
    (emissions : List (RuleEmission Nat))
    (permuted : (fusedDrain admitted type subject).emissions.Perm emissions) :
    Multiset.Rel (SameOccurrence source.core provider)
      (((authoredDrain admitted type subject).publication.map receiptReadout) : Multiset RootReadout)
      (emissions : Multiset (RuleEmission Nat)) := by
  rw [← Multiset.coe_eq_coe.mpr permuted]
  exact completed_occurrence_bags admitted shape typed

theorem retained_occurrence_bags {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {bound : List TypeExpr} {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free bound type subject)
    (budget : GeneralRuleJobs.Job → Nat) (fuel : Nat) :
    let authored := authoredProgram admitted bound type subject budget
    let fused := OrderedMatchMachineLanguage.runFrontier (providerRelEnv provider) source.core fuel
      (OrderedMatchMachineLanguage.startFrontier (machineProgram admitted type) subject)
    Multiset.Rel (SameOccurrence source.core provider)
      (((authored.publication ++ authored.withheld).map receiptReadout) : Multiset RootReadout)
      ((fused.emissions ++ OrderedMatchMachineLanguage.frontierEmissions (providerRelEnv provider)
        source.core fused.pending) : Multiset (RuleEmission Nat)) :=
  Mettapedia.GSLT.Distinction.OccurrenceSimulation.forall₂_multisetRel
    (retained_realizations admitted shape typed budget fuel)

theorem finite_frontier_bags {source : OrderedFirstOrderAdmission.Source}
    {provider : GeneralPremise.ProviderSnapshot}
    (admitted : OrderedFirstOrderAdmission.Admitted source provider)
    {type : TypeExpr} {subject : Pattern}
    (shape : GeneralFirstOrderProjection.FirstOrder subject)
    (typed : OpenPatternWellSorted (environment source.core provider).language
      (environment source.core provider).free [] type subject) (count : Nat) :
    Multiset.Rel SameBoundary
      (((authoredSystem admitted type).runFrontier count [Boundary.start RootReadout shape typed]) :
        Multiset (Boundary source.core provider type RootReadout))
      (((fusedSystem admitted type).runFrontier count [Boundary.start (RuleEmission Nat) shape typed]) :
        Multiset (Boundary source.core provider type (RuleEmission Nat))) :=
  Mettapedia.GSLT.Distinction.OccurrenceSimulation.forall₂_multisetRel
    (subject_frontiers admitted shape typed count)

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.OrderedRealizations
