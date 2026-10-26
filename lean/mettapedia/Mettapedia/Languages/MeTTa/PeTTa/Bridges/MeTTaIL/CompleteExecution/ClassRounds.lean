import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassSearch

/-!
# Steps modulo equations: rounds

The lanes of a representative, a lane's events, one unit of work per lane, the discovery of new
members, and the rounds, as `Complete.Classes` computes them, on every ready state.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.WellSorted (checkOpenPatternWellSorted FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise ScopedRuleMatching RuleBinding DerivedContexts GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (Scope Declared OutcomeWithin FiringWithin KeyReady ClassReady)
open GeneralOccurrenceSemantics (Conversion)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval
open BridgeKit WireKit
open DescentCodec

variable (plan : GeneralExecutionAdmission.Plan)

/-- What the payloads of a lane satisfy for their events to be computed. -/
def PayloadsReady (footprint : List String) :
    (key : Complete.Classes.Key) → List (Complete.Classes.family plan key).Payload → Prop
  | .rule _ job, payloads => ∀ firing ∈ payloads, LiftReady plan job footprint firing
  | .forward _ _, payloads => ∀ outcome ∈ payloads, OutcomeWithin footprint outcome
  | .backward _ _ _, payloads => ∀ outcome ∈ payloads, OutcomeWithin footprint outcome

@[metta_head "gslt:classes:events"]
theorem classes_events_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (key : Complete.Classes.Key) (licensed : KeyLicensed plan bound expected key)
    (payloads : List (Complete.Classes.family plan key).Payload) (ready : PayloadsReady plan footprint key payloads) :
    PureReturns runtime [] state
      (apply "gslt:classes:events" [planValue plan table bound expected, encoded (keyTerm key),
        encoded (encodeList (wireOf plan key).payload payloads)])
      state (encoded (encodeList eventTerm (Complete.Classes.events plan bound expected key payloads))) := by
  cases key with
  | rule rep job =>
    have receipts := step_lift_returns plan state table bound expected footprint tabled rep.pattern job licensed
      payloads ready
    have events := firing_events_returns state rep.pattern rep.conversions
      (payloads.filterMap (Complete.Step.lift plan bound expected job))
    complete_eval [receipts, events]
      unfolding [keyTerm, repTerm, wireOf, rootWire, planValue, CompletePlanWire.planTerm, Complete.Classes.events,
        patternValue]
  | forward rep lane =>
    have events := forward_events_returns plan state table bound expected footprint tabled scope rep.pattern lane
      licensed rep.conversions payloads ready
    complete_eval [events] unfolding [keyTerm, repTerm, wireOf, premisesWire, Complete.Classes.events]
  | backward rep candidate lane =>
    have events := backward_events_returns plan state table bound expected footprint tabled scope rep.pattern
      candidate lane licensed rep.conversions payloads ready
    complete_eval [events] unfolding [keyTerm, repTerm, wireOf, premisesWire, Complete.Classes.events, patternValue]

/-- How `gslt:classes:keys` labels a lane. -/
inductive KeyKind where
  | rule
  | forward
  | backward (candidate : Pattern)

def KeyKind.term : KeyKind → Term
  | .rule => .symbol "RuleKind"
  | .forward => .symbol "ForwardKind"
  | .backward candidate => .application "BackwardKind" [InferenceCettaWire.encodePattern candidate]

@[metta_head "gslt:classes:keys"]
theorem rule_keys_returns (state : State) (rep : Complete.Classes.Rep) : ∀ jobs : List GeneralRuleJobs.Job,
    PureReturns runtime [] state
      (apply "gslt:classes:keys" [encoded KeyKind.rule.term, encoded (repTerm rep),
        encoded (encodeList ScopedRuleJobReadoutExecution.jobTerm jobs)])
      state (encoded (encodeList keyTerm (jobs.map (Complete.Classes.Key.rule rep))))
  | [] => by
    complete_eval unfolding [encodeList]
  | job :: rest => by
    have later := rule_keys_returns state rep rest
    complete_eval [later] unfolding [encodeList, KeyKind.term, keyTerm, List.map_cons]

theorem forward_keys_returns (state : State) (rep : Complete.Classes.Rep) : ∀ lanes : List Complete.EquationJob.Lane,
    PureReturns runtime [] state
      (apply "gslt:classes:keys" [encoded KeyKind.forward.term, encoded (repTerm rep), encoded (encodeList laneTerm lanes)])
      state (encoded (encodeList keyTerm (lanes.map (Complete.Classes.Key.forward rep))))
  | [] => by
    complete_eval unfolding [encodeList]
  | lane :: rest => by
    have later := forward_keys_returns state rep rest
    complete_eval [later] unfolding [encodeList, KeyKind.term, keyTerm, List.map_cons]

theorem backward_keys_of_returns (state : State) (rep : Complete.Classes.Rep) (candidate : Pattern) :
    ∀ lanes : List Complete.EquationJob.Lane,
      PureReturns runtime [] state
        (apply "gslt:classes:keys" [encoded (KeyKind.backward candidate).term, encoded (repTerm rep),
          encoded (encodeList laneTerm lanes)])
        state (encoded (encodeList keyTerm (lanes.map (Complete.Classes.Key.backward rep candidate))))
  | [] => by
    complete_eval unfolding [encodeList]
  | lane :: rest => by
    have later := backward_keys_of_returns state rep candidate rest
    complete_eval [later] unfolding [encodeList, KeyKind.term, keyTerm, List.map_cons]

/-- `gslt:equations:lanes` on any term, sorted or not, when the footprint lists every declared name. -/
theorem lanes_declared_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (source : Pattern) :
    PureReturns runtime [] state
      (apply "gslt:equations:lanes" [planValue plan table bound expected, patternValue source])
      state (encoded (encodeList laneTerm (Complete.EquationJob.lanes plan bound expected source))) := by
  by_cases sorted : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
      bound expected source = true
  · exact lanes_returns plan state table bound expected footprint tabled source
      (Complete.Footprint.sorted_within declared sorted)
  · have untyped : checkOpenPatternWellSorted (GeneralPlanEnvironment.environment plan).language plan.snapshot.free
        bound expected source = false := Bool.eq_false_iff.mpr sorted
    have checked := complete_sorted_returns state (GeneralPlanEnvironment.environment plan).language table bound
      expected source
    subst tabled
    rw [Complete.Footprint.full_table declared] at checked
    rw [show Complete.EquationJob.lanes plan bound expected source = [] by simp [Complete.EquationJob.lanes, untyped]]
    complete_eval [checked]
      unfolding [planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
        untyped, encodeList, patternValue]

@[metta_head "gslt:classes:backward-keys"]
theorem backward_keys_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (rep : Complete.Classes.Rep) : ∀ candidates : List Pattern,
      PureReturns runtime [] state
        (apply "gslt:classes:backward-keys" [planValue plan table bound expected, encoded (repTerm rep),
          patternsValue candidates])
        state (encoded (encodeList keyTerm (candidates.flatMap fun candidate =>
          (Complete.EquationJob.lanes plan bound expected candidate).map (Complete.Classes.Key.backward rep candidate))))
  | [] => by
    complete_eval unfolding [patternsValue, InferenceCettaWire.encodePatterns, encodeList]
  | candidate :: rest => by
    have lanes := lanes_declared_returns plan state table bound expected footprint tabled declared candidate
    have keys := backward_keys_of_returns state rep candidate (Complete.EquationJob.lanes plan bound expected candidate)
    have later := backward_keys_returns state table bound expected footprint tabled declared rep rest
    have joined := complete_append_returns keyTerm state
      ((Complete.EquationJob.lanes plan bound expected candidate).map (Complete.Classes.Key.backward rep candidate))
      (rest.flatMap fun candidate =>
        (Complete.EquationJob.lanes plan bound expected candidate).map (Complete.Classes.Key.backward rep candidate))
    complete_eval [lanes, keys, later, joined]
      unfolding [patternsValue, InferenceCettaWire.encodePatterns, encodeList, KeyKind.term, List.flatMap_cons, patternValue]

@[metta_head "gslt:classes:lanes"]
theorem classes_lanes_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (rep : Complete.Classes.Rep)
    (inside : ∀ name ∈ rep.pattern.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (apply "gslt:classes:lanes" [planValue plan table bound expected, encoded (repTerm rep)])
      state (encoded (encodeList keyTerm (Complete.Classes.lanesOf plan bound expected rep))) := by
  have jobs := complete_jobs_returns state plan bound expected rep.pattern footprint inside
  have ruleKeys := rule_keys_returns state rep (GeneralRuleJobs.jobs plan bound expected rep.pattern)
  have forward := lanes_declared_returns plan state table bound expected footprint tabled declared rep.pattern
  have forwardKeys := forward_keys_returns state rep (Complete.EquationJob.lanes plan bound expected rep.pattern)
  have candidates := predecessors_returns state plan table bound expected rep.pattern
  have backward := backward_keys_returns plan state table bound expected footprint tabled declared rep
    (Complete.Predecessors.predecessors plan bound rep.pattern)
  have early := complete_append_returns keyTerm state
    ((GeneralRuleJobs.jobs plan bound expected rep.pattern).map (Complete.Classes.Key.rule rep))
    ((Complete.EquationJob.lanes plan bound expected rep.pattern).map (Complete.Classes.Key.forward rep))
  have all := complete_append_returns keyTerm state
    ((GeneralRuleJobs.jobs plan bound expected rep.pattern).map (Complete.Classes.Key.rule rep) ++
      (Complete.EquationJob.lanes plan bound expected rep.pattern).map (Complete.Classes.Key.forward rep))
    ((Complete.Predecessors.predecessors plan bound rep.pattern).flatMap fun candidate =>
      (Complete.EquationJob.lanes plan bound expected candidate).map (Complete.Classes.Key.backward rep candidate))
  subst tabled
  complete_eval [jobs, ruleKeys, forward, forwardKeys, candidates, backward, early, all]
    unfolding [planValue, CompletePlanWire.planTerm, PremiseOperationsExecution.GeneralExecution.environmentTerm,
      PremiseOperationsExecution.DeclarationTyping.declarationsTerm,
      PremiseOperationsExecution.DeclarationTyping.boundContextTerm, repTerm, KeyKind.term, Complete.Classes.lanesOf,
      patternValue]

theorem lanes_licensed {bound : List TypeExpr} {expected : TypeExpr} {rep : Complete.Classes.Rep}
    {key : Complete.Classes.Key} (member : key ∈ Complete.Classes.lanesOf plan bound expected rep) :
    KeyLicensed plan bound expected key := by
  simp only [Complete.Classes.lanesOf, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with (⟨job, listed, rfl⟩ | ⟨lane, listed, rfl⟩) | ⟨candidate, _, lane, listed, rfl⟩
  · exact (GeneralRuleJobs.jobs_spec plan bound expected rep.pattern job).mp listed
  · exact listed
  · exact listed

@[metta_head "gslt:classes:start-entries"]
theorem start_entries_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) : ∀ keys : List Complete.Classes.Key, (∀ key ∈ keys, KeyLicensed plan bound expected key) →
      PureReturns runtime [] state
        (apply "gslt:classes:start-entries" [planValue plan table bound expected, encoded (encodeList keyTerm keys)])
        state (encoded (encodeList (classEntryTerm plan)
          (keys.map fun key => (⟨key, Complete.Deep.start (Complete.Classes.family plan key)⟩ :
            Complete.Classes.Entry plan))))
  | [], _ => by
    complete_eval unfolding [encodeList]
  | key :: rest, licensed => by
    have family := classes_family_returns plan state table bound expected key (licensed key (by simp))
    have started := deep_start_returns (wireOf plan key) state
    have later := start_entries_returns state table bound expected rest
      (fun other member => licensed other (by simp [member]))
    complete_eval [family, started, later] unfolding [encodeList, classEntryTerm, List.map_cons]

@[metta_head "gslt:classes:reps-lanes"]
theorem reps_lanes_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) : ∀ reps : List Complete.Classes.Rep,
      (∀ rep ∈ reps, ∀ name ∈ rep.pattern.freeFvarNames, name ∈ footprint) →
      PureReturns runtime [] state
        (apply "gslt:classes:reps-lanes" [planValue plan table bound expected, encoded (encodeList repTerm reps)])
        state (encoded (encodeList keyTerm (reps.flatMap (Complete.Classes.lanesOf plan bound expected))))
  | [], _ => by
    complete_eval unfolding [encodeList]
  | rep :: rest, inside => by
    have here := classes_lanes_returns plan state table bound expected footprint tabled declared rep
      (inside rep (by simp))
    have later := reps_lanes_returns state table bound expected footprint tabled declared rest
      (fun other member => inside other (by simp [member]))
    have joined := complete_append_returns keyTerm state (Complete.Classes.lanesOf plan bound expected rep)
      (rest.flatMap (Complete.Classes.lanesOf plan bound expected))
    complete_eval [here, later, joined] unfolding [encodeList, List.flatMap_cons]

@[metta_head "gslt:classes:begin"]
theorem classes_begin_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (declared : Declared plan footprint) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ footprint) :
    PureReturns runtime [] state
      (apply "gslt:classes:begin" [planValue plan table bound expected, patternValue source])
      state (encoded (classStateTerm plan (Complete.Classes.begin plan bound expected source))) := by
  have keys := classes_lanes_returns plan state table bound expected footprint tabled declared ⟨source, [], 0⟩ inside
  have entries := start_entries_returns plan state table bound expected
    (Complete.Classes.lanesOf plan bound expected ⟨source, [], 0⟩) (fun _ member => lanes_licensed plan member)
  complete_eval [keys, entries]
    unfolding [classStateTerm, Complete.Classes.begin, repTerm, encodeList, patternValue]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
