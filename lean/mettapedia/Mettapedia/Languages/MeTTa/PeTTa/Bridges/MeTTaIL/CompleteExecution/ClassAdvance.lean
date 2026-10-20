import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRounds

/-!
# Steps modulo equations: units of work, discoveries and rounds

`gslt:classes:advance` gives a lane one unit of work and turns its newly published payloads into
events; `round` advances every lane, adds the discovered members with fresh lanes and appends the
firings to the log; `rounds` repeats it. Each is the model's on ready states.
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

/-- One unit of work for a lane, as MeTTa data: `(ClassAdvanced entry events)`. -/
def classAdvancedTerm (advanced : Complete.Classes.Entry plan × List Complete.Classes.Event) : Term :=
  .application "ClassAdvanced" [classEntryTerm plan advanced.1, encodeList eventTerm advanced.2]

syntax "advance_eval" " [" term,* "]" : tactic
macro_rules
  | `(tactic| advance_eval [$facts,*]) => `(tactic|
      complete_eval [$facts,*]
        unfolding [planValue, CompletePlanWire.planTerm, classEntryTerm, classAdvancedTerm, Complete.Classes.advance,
          wireOf, rootWire, premisesWire, environmentValue])

@[metta_head "gslt:classes:advance"]
theorem classes_advance_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (entry : Complete.Classes.Entry plan)
    (ready : KeyReady plan bound expected footprint entry.1 entry.2) :
    PureReturns runtime [] state
      (apply "gslt:classes:advance" [planValue plan table bound expected, encoded (classEntryTerm plan entry)])
      state (encoded (classAdvancedTerm plan (Complete.Classes.advance plan bound expected entry))) := by
  obtain ⟨key, deep⟩ := entry
  have freeSame : (GeneralPlanEnvironment.environment plan).free = plan.snapshot.free := rfl
  cases key with
  | rule rep job =>
    have licensed : KeyLicensed plan bound expected (.rule rep job) := ready.1
    have family := classes_family_returns plan state table bound expected _ licensed
    have before := deep_publication_returns (wireOf plan (.rule rep job)) state deep
    have count := complete_length_returns (wireOf plan (.rule rep job)).payload state deep.publication
    have level := complete_descent_tick_returns state (GeneralPlanEnvironment.environment plan) scope.finite footprint
      scope.provider _ deep.level ready.2.2.2.level
    have ticked := deep_tick_returns (wireOf plan (.rule rep job)) state _ deep level
    have after := deep_publication_returns (wireOf plan (.rule rep job)) state
      (Complete.Deep.tick (Complete.Classes.family plan (.rule rep job)) deep)
    have fresh := drop_list_returns (wireOf plan (.rule rep job)).payload state deep.publication.length
      (Complete.Deep.tick (Complete.Classes.family plan (.rule rep job)) deep).publication
    have next := Complete.Footprint.key_ready_tick scope ready
    have events := classes_events_returns plan state table bound expected footprint tabled scope (.rule rep job)
      licensed ((Complete.Deep.tick (Complete.Classes.family plan (.rule rep job)) deep).publication.drop
        deep.publication.length)
      (fun firing member => ⟨Complete.Deep.publication_valid _ next.2.2.1 firing (List.mem_of_mem_drop member),
        Complete.Deep.publication_covered (Complete.Footprint.job_footprinted scope ready.1 ready.2.1) next.2.2.2
          firing (List.mem_of_mem_drop member)⟩)
    subst tabled
    advance_eval [family, before, count, ticked, after, fresh, events]
  | forward rep lane =>
    have licensed : KeyLicensed plan bound expected (.forward rep lane) := ready.1
    have family := classes_family_returns plan state table bound expected _ licensed
    have before := deep_publication_returns (wireOf plan (.forward rep lane)) state deep
    have count := complete_length_returns (wireOf plan (.forward rep lane)).payload state deep.publication
    have level := complete_descent_tick_returns state (GeneralPlanEnvironment.environment plan) scope.finite footprint
      scope.provider _ deep.level ready.2.2.level
    have ticked := deep_tick_returns (wireOf plan (.forward rep lane)) state _ deep level
    have after := deep_publication_returns (wireOf plan (.forward rep lane)) state
      (Complete.Deep.tick (Complete.Classes.family plan (.forward rep lane)) deep)
    have fresh := drop_list_returns (wireOf plan (.forward rep lane)).payload state deep.publication.length
      (Complete.Deep.tick (Complete.Classes.family plan (.forward rep lane)) deep).publication
    have next := Complete.Footprint.key_ready_tick scope ready
    have events := classes_events_returns plan state table bound expected footprint tabled scope (.forward rep lane)
      licensed ((Complete.Deep.tick (Complete.Classes.family plan (.forward rep lane)) deep).publication.drop
        deep.publication.length)
      (fun outcome member => Complete.Deep.publication_covered (Complete.Footprint.lane_footprinted scope ready.1)
        next.2.2 outcome (List.mem_of_mem_drop member))
    subst tabled
    advance_eval [family, before, count, ticked, after, fresh, events]
  | backward rep candidate lane =>
    have licensed : KeyLicensed plan bound expected (.backward rep candidate lane) := ready.1
    have family := classes_family_returns plan state table bound expected _ licensed
    have before := deep_publication_returns (wireOf plan (.backward rep candidate lane)) state deep
    have count := complete_length_returns (wireOf plan (.backward rep candidate lane)).payload state deep.publication
    have level := complete_descent_tick_returns state (GeneralPlanEnvironment.environment plan) scope.finite footprint
      scope.provider _ deep.level ready.2.2.level
    have ticked := deep_tick_returns (wireOf plan (.backward rep candidate lane)) state _ deep level
    have after := deep_publication_returns (wireOf plan (.backward rep candidate lane)) state
      (Complete.Deep.tick (Complete.Classes.family plan (.backward rep candidate lane)) deep)
    have fresh := drop_list_returns (wireOf plan (.backward rep candidate lane)).payload state deep.publication.length
      (Complete.Deep.tick (Complete.Classes.family plan (.backward rep candidate lane)) deep).publication
    have next := Complete.Footprint.key_ready_tick scope ready
    have events := classes_events_returns plan state table bound expected footprint tabled scope
      (.backward rep candidate lane) licensed
      ((Complete.Deep.tick (Complete.Classes.family plan (.backward rep candidate lane)) deep).publication.drop
        deep.publication.length)
      (fun outcome member => Complete.Deep.publication_covered (Complete.Footprint.lane_footprinted scope ready.1)
        next.2.2 outcome (List.mem_of_mem_drop member))
    subst tabled
    advance_eval [family, before, count, ticked, after, fresh, events]

@[metta_head "gslt:classes:represented"]
theorem represented_returns (state : State) (pattern : Pattern) : ∀ reps : List Complete.Classes.Rep,
    PureReturns runtime [] state
      (apply "gslt:classes:represented" [patternValue pattern, encoded (encodeList repTerm reps)])
      state (Effects.boolean (reps.any fun rep => rep.pattern == pattern))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | rep :: rest => by
    have later := represented_returns state pattern rest
    by_cases same : (rep.pattern == pattern) = true
    · have equal : InferenceCettaWire.encodePattern rep.pattern = InferenceCettaWire.encodePattern pattern :=
        congrArg InferenceCettaWire.encodePattern (beq_iff_eq.mp same)
      metta_call complete_checked
      metta_eval unfolding [encodeList, repTerm]
      all_goals
        rw [if_pos equal]
        simp only [same, List.any_cons, Bool.true_or]
        metta_eval
    · have different : InferenceCettaWire.encodePattern rep.pattern ≠ InferenceCettaWire.encodePattern pattern :=
        fun equal => same (beq_iff_eq.mpr (InferenceCettaWire.encodePattern_injective equal))
      metta_call complete_checked
      metta_eval unfolding [encodeList, repTerm]
      all_goals
        rw [if_neg different]
        simp only [Bool.eq_false_iff.mpr same, List.any_cons, Bool.false_or]
        metta_eval [later] with complete_checked
          unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
            Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
            Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?]

@[metta_head "gslt:classes:add-discoveries"]
theorem add_discoveries_returns (state : State) (born : Nat) : ∀ (events : List Complete.Classes.Event)
    (reps : List Complete.Classes.Rep),
    PureReturns runtime [] state
      (apply "gslt:classes:add-discoveries" [number born, encoded (encodeList repTerm reps),
        encoded (encodeList eventTerm events)])
      state (encoded (encodeList repTerm (Complete.Classes.addDiscoveries born reps events)))
  | [], reps => by
    metta_call complete_checked
    metta_eval unfolding [encodeList, Complete.Classes.addDiscoveries]
  | .firing receipt :: rest, reps => by
    have later := add_discoveries_returns state born rest reps
    rw [Complete.Classes.addDiscoveries]
    complete_eval [later] unfolding [encodeList, eventTerm]
  | .discovery pattern conversions :: rest, reps => by
    have represented := represented_returns state pattern reps
    rw [Complete.Classes.addDiscoveries]
    by_cases found : (reps.any fun rep => rep.pattern == pattern) = true
    · rw [if_pos found]
      have later := add_discoveries_returns state born rest reps
      complete_eval [represented, later] unfolding [encodeList, eventTerm, found]
    · rw [if_neg found]
      have grown := complete_append_returns repTerm state reps [⟨pattern, conversions, born⟩]
      have later := add_discoveries_returns state born rest (reps ++ [⟨pattern, conversions, born⟩])
      complete_eval [represented, grown, later]
        unfolding [encodeList, eventTerm, Bool.eq_false_iff.mpr found, repTerm, patternValue]

@[metta_head "gslt:classes:firings"]
theorem classes_firings_returns (state : State) : ∀ events : List Complete.Classes.Event,
    PureReturns runtime [] state (apply "gslt:classes:firings" [encoded (encodeList eventTerm events)])
      state (encoded (encodeList classReceiptTerm (Complete.Classes.firings events)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList, Complete.Classes.firings]
  | .firing receipt :: rest => by
    have later := classes_firings_returns state rest
    complete_eval [later] unfolding [encodeList, eventTerm, Complete.Classes.firings]
  | .discovery pattern conversions :: rest => by
    have later := classes_firings_returns state rest
    complete_eval [later] unfolding [encodeList, eventTerm, Complete.Classes.firings]

/-- One unit of work for every lane, as MeTTa data. -/
def classAdvancedAllTerm (advanced : List (Complete.Classes.Entry plan) × List Complete.Classes.Event) : Term :=
  .application "ClassAdvanced" [encodeList (classEntryTerm plan) advanced.1, encodeList eventTerm advanced.2]

@[metta_head "gslt:classes:advance-all"]
theorem classes_advance_all_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) : ∀ entries : List (Complete.Classes.Entry plan),
      (∀ entry ∈ entries, KeyReady plan bound expected footprint entry.1 entry.2) →
      PureReturns runtime [] state
        (apply "gslt:classes:advance-all" [planValue plan table bound expected,
          encoded (encodeList (classEntryTerm plan) entries)])
        state (encoded (classAdvancedAllTerm plan
          ((entries.map (Complete.Classes.advance plan bound expected)).map Prod.fst,
            (entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd)))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList, classAdvancedAllTerm]
  | entry :: rest, ready => by
    have head := classes_advance_returns plan state table bound expected footprint tabled scope entry
      (ready entry (by simp))
    have tail := classes_advance_all_returns state table bound expected footprint tabled scope rest
      (fun other member => ready other (by simp [member]))
    have joined := complete_append_returns eventTerm state (Complete.Classes.advance plan bound expected entry).2
      ((rest.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd)
    complete_eval [head, tail, joined]
      unfolding [encodeList, classAdvancedAllTerm, classAdvancedTerm, List.map_cons, List.flatMap_cons]

@[metta_head "gslt:classes:round"]
theorem classes_round_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) (search : Complete.Classes.State plan)
    (ready : ClassReady plan bound expected footprint search) :
    PureReturns runtime [] state
      (apply "gslt:classes:round" [planValue plan table bound expected, encoded (classStateTerm plan search)])
      state (encoded (classStateTerm plan (Complete.Classes.round plan bound expected search))) := by
  obtain ⟨round, reps, entries, log⟩ := search
  have advanced := classes_advance_all_returns plan state table bound expected footprint tabled scope entries
    ready.entries
  have discovered := add_discoveries_returns state (round + 1) ((entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd) reps
  have count := complete_length_returns repTerm state reps
  have fresh := drop_list_returns repTerm state reps.length (Complete.Classes.addDiscoveries (round + 1) reps ((entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd))
  have nextReady := Complete.Footprint.ready_round scope ready
  have keys := reps_lanes_returns plan state table bound expected footprint tabled scope.declared ((Complete.Classes.addDiscoveries (round + 1) reps ((entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd)).drop reps.length)
    (fun rep member => nextReady.reps rep (List.mem_of_mem_drop member))
  have entriesFresh := start_entries_returns plan state table bound expected
    (((Complete.Classes.addDiscoveries (round + 1) reps ((entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd)).drop reps.length).flatMap (Complete.Classes.lanesOf plan bound expected))
    (fun key member => by
      obtain ⟨rep, _, inside⟩ := List.mem_flatMap.mp member
      exact lanes_licensed plan inside)
  have all := complete_append_returns (classEntryTerm plan) state
    ((entries.map (Complete.Classes.advance plan bound expected)).map Prod.fst)
    ((((Complete.Classes.addDiscoveries (round + 1) reps ((entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd)).drop reps.length).flatMap (Complete.Classes.lanesOf plan bound expected)).map fun key =>
      (⟨key, Complete.Deep.start (Complete.Classes.family plan key)⟩ : Complete.Classes.Entry plan))
  have firings := classes_firings_returns state ((entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd)
  have published := complete_append_returns classReceiptTerm state log (Complete.Classes.firings ((entries.map (Complete.Classes.advance plan bound expected)).flatMap Prod.snd))
  complete_eval [advanced, discovered, count, fresh, keys, entriesFresh, all, firings, published]
    unfolding [classStateTerm, classAdvancedAllTerm, Complete.Classes.round]

@[metta_head "gslt:classes:rounds"]
theorem classes_rounds_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (footprint : List String) (tabled : table = plan.snapshot.free.entriesOn footprint)
    (scope : Scope plan footprint) :
    ∀ (work : Nat) (search : Complete.Classes.State plan), ClassReady plan bound expected footprint search →
      PureReturns runtime [] state
        (apply "gslt:classes:rounds" [planValue plan table bound expected, number work,
          encoded (classStateTerm plan search)])
        state (encoded (classStateTerm plan (Complete.Classes.rounds plan bound expected work search)))
  | 0, search, _ => by
    metta_call complete_checked
    metta_eval unfolding [Complete.Classes.rounds]
  | work + 1, search, ready => by
    have once := classes_round_returns plan state table bound expected footprint tabled scope search ready
    have later := classes_rounds_returns state table bound expected footprint tabled scope work
      (Complete.Classes.round plan bound expected search) (Complete.Footprint.ready_round scope ready)
    complete_eval [once, later] unfolding [Complete.Classes.rounds]

@[metta_head "gslt:classes:entries-complete"]
theorem classes_entries_complete_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) : ∀ entries : List (Complete.Classes.Entry plan),
      (∀ entry ∈ entries, KeyLicensed plan bound expected entry.1) →
      PureReturns runtime [] state
        (apply "gslt:classes:entries-complete" [planValue plan table bound expected,
          encoded (encodeList (classEntryTerm plan) entries)])
        state (Effects.boolean (entries.all fun entry => entry.2.complete))
  | [], _ => by
    metta_call complete_checked
    metta_eval unfolding [encodeList]
  | ⟨key, deep⟩ :: rest, licensed => by
    have family := classes_family_returns plan state table bound expected key (licensed ⟨key, deep⟩ (by simp))
    have done := deep_complete_returns (wireOf plan key) state deep
    have later := classes_entries_complete_returns state table bound expected rest
      (fun other member => licensed other (by simp [member]))
    cases finished : deep.complete
    · complete_eval [family, done] unfolding [encodeList, classEntryTerm, finished, List.all_cons]
    · complete_eval [family, done, later] unfolding [encodeList, classEntryTerm, finished, List.all_cons]

@[metta_head "gslt:classes:patterns"]
theorem classes_patterns_returns (state : State) : ∀ reps : List Complete.Classes.Rep,
    PureReturns runtime [] state (apply "gslt:classes:patterns" [encoded (encodeList repTerm reps)])
      state (patternsValue (reps.map (·.pattern)))
  | [] => by
    metta_call complete_checked
    metta_eval unfolding [encodeList, patternsValue, InferenceCettaWire.encodePatterns]
  | rep :: rest => by
    have later := classes_patterns_returns state rest
    complete_eval [later] unfolding [encodeList, repTerm, patternsValue, InferenceCettaWire.encodePatterns, List.map_cons]

/-- The readout of a classes state: its members, its log, and whether every lane is complete. -/
def classReadoutValue (search : Complete.Classes.State plan) : Atom :=
  .expression [.symbol "ClassReadout", patternsValue (search.reps.map (·.pattern)),
    encoded (encodeList classReceiptTerm search.log), Effects.boolean (Complete.Classes.complete plan search)]

@[metta_head "gslt:classes:readout"]
theorem classes_readout_returns (state : State) (table : List (String × TypeExpr)) (bound : List TypeExpr)
    (expected : TypeExpr) (search : Complete.Classes.State plan)
    (licensed : ∀ entry ∈ search.entries, KeyLicensed plan bound expected entry.1) :
    PureReturns runtime [] state
      (apply "gslt:classes:readout" [planValue plan table bound expected, encoded (classStateTerm plan search)])
      state (classReadoutValue plan search) := by
  obtain ⟨round, reps, entries, log⟩ := search
  have patterns := classes_patterns_returns state reps
  have complete := classes_entries_complete_returns plan state table bound expected entries licensed
  complete_eval [patterns, complete] unfolding [classStateTerm, classReadoutValue, Complete.Classes.complete]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
