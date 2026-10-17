import Mettapedia.OSLF.MeTTaIL.Complete.Step
import Mettapedia.OSLF.MeTTaIL.Complete.EquationJob
import Mettapedia.OSLF.MeTTaIL.Complete.Predecessors

/-!
# Steps modulo equations, complete in the limit

The steps of a plan's GSLT are rule firings at any term equal to the source, modulo the plan's
equations (`GeneralOccurrenceSemantics.gslt`). This search explores the source's equality class
and fires rules at every member it reaches.

A *representative* is a member of the class with a conversion path from the source. Each
representative runs three kinds of lanes, all deepening searches (`Complete.Deep`):

- **rule lanes**: its rule jobs (`Complete.Step`); their firings are the published receipts;
- **forward lanes**: its equation jobs (`Complete.EquationJob`); each instance's target is a
  member of the class;
- **backward lanes**: the equation jobs at each predecessor candidate (`Complete.Predecessors`);
  an instance whose target is the representative makes the candidate a member.

A round gives every lane one unit of work, then adds every newly found member as a representative
with fresh lanes. No term universe is enumerated.

- `sound`: every published receipt is a valid step receipt at the source;
- `complete_in_limit`: every step of the GSLT from the source is published, up to equality of
  targets, after finitely many rounds;
- `exact_of_complete`: once every lane is certified, every step is published.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Complete.Classes

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission
open GeneralOccurrenceSemantics (Conversion ConversionPath)

variable (plan : Plan) (bound : List TypeExpr) (expected : TypeExpr)

/-- A member of the class, with its conversions from the source and the round it was found. -/
structure Rep where
  pattern : Pattern
  conversions : List Conversion
  born : Nat

/-- A lane of a representative. -/
inductive Key where
  | rule (rep : Rep) (job : GeneralRuleJobs.Job)
  | forward (rep : Rep) (lane : EquationJob.Lane)
  | backward (rep : Rep) (candidate : Pattern) (lane : EquationJob.Lane)

def Key.rep : Key → Rep
  | .rule rep _ => rep
  | .forward rep _ => rep
  | .backward rep _ _ => rep

/-- The deepening search of a lane. -/
abbrev family : Key → Deep.Family
  | .rule _ job => DeepRoot.family (Step.request plan job)
  | .forward _ lane => EquationJob.family plan lane
  | .backward _ _ lane => EquationJob.family plan lane

/-- What newly published payloads of a lane give: step receipts, or new members. -/
inductive Event where
  | firing (receipt : GeneralOccurrenceSemantics.Receipt)
  | discovery (pattern : Pattern) (conversions : List Conversion)

/-- The events of payloads of a lane. -/
def events : (key : Key) → List (family plan key).Payload → List Event
  | .rule rep job, payloads =>
      (payloads.filterMap (Step.lift plan bound expected job)).map fun firing =>
        .firing ⟨rep.pattern, rep.conversions, firing⟩
  | .forward rep lane, payloads =>
      (payloads.filterMap (EquationJob.lift plan bound expected lane)).map fun receipt =>
        .discovery receipt.target (rep.conversions ++ [.forward receipt])
  | .backward rep candidate lane, payloads =>
      ((payloads.filterMap (EquationJob.lift plan bound expected lane)).filter fun receipt =>
        receipt.target == rep.pattern).map fun receipt =>
        .discovery candidate (rep.conversions ++ [.reverse receipt])

/-- The lanes of a representative. -/
def lanesOf (rep : Rep) : List Key :=
  (GeneralRuleJobs.jobs plan bound expected rep.pattern).map (.rule rep) ++
    (EquationJob.lanes plan bound expected rep.pattern).map (.forward rep) ++
    (Predecessors.predecessors plan bound rep.pattern).flatMap fun candidate =>
      (EquationJob.lanes plan bound expected candidate).map (.backward rep candidate)

/-- A lane with its deepening search. -/
abbrev Entry := Σ key : Key, Deep.State (family plan key)

/-- The search: the round, the representatives, every lane, and the published receipts. -/
structure State where
  round : Nat
  reps : List Rep
  entries : List (Entry plan)
  log : List GeneralOccurrenceSemantics.Receipt

/-- Add discovered members not yet represented. -/
def addDiscoveries (born : Nat) : List Rep → List Event → List Rep
  | reps, [] => reps
  | reps, .firing _ :: rest => addDiscoveries born reps rest
  | reps, .discovery pattern conversions :: rest =>
      if reps.any (fun rep => rep.pattern == pattern) then addDiscoveries born reps rest
      else addDiscoveries born (reps ++ [⟨pattern, conversions, born⟩]) rest

/-- The receipts among events. -/
def firings : List Event → List GeneralOccurrenceSemantics.Receipt
  | [] => []
  | .firing receipt :: rest => receipt :: firings rest
  | .discovery _ _ :: rest => firings rest

/-- One unit of work for a lane, and the events of its newly published payloads. -/
def advance (entry : Entry plan) : Entry plan × List Event :=
  let next := Deep.tick (family plan entry.1) entry.2
  (⟨entry.1, next⟩, events plan bound expected entry.1 (next.publication.drop entry.2.publication.length))

/-- One round: every lane gets one unit of work; new members join with fresh lanes. -/
def round (state : State plan) : State plan :=
  let advanced := state.entries.map (advance plan bound expected)
  let found := advanced.flatMap Prod.snd
  let reps := addDiscoveries (state.round + 1) state.reps found
  ⟨state.round + 1, reps,
    advanced.map Prod.fst ++ ((reps.drop state.reps.length).flatMap (lanesOf plan bound expected)).map
      fun key => ⟨key, Deep.start (family plan key)⟩,
    state.log ++ firings found⟩

/-- `work` rounds. -/
def rounds : Nat → State plan → State plan
  | 0, state => state
  | work + 1, state => rounds work (round plan bound expected state)

/-- The source as the first representative. -/
def begin (source : Pattern) : State plan :=
  let rep : Rep := ⟨source, [], 0⟩
  ⟨0, [rep], (lanesOf plan bound expected rep).map fun key => ⟨key, Deep.start (family plan key)⟩, []⟩

/-- Every lane is certified and drained. -/
def complete (state : State plan) : Bool := state.entries.all fun entry => entry.2.complete

/-! ## Basic facts -/

theorem rounds_succ (work : Nat) (state : State plan) :
    rounds plan bound expected (work + 1) state = round plan bound expected (rounds plan bound expected work state) := by
  induction work generalizing state with
  | zero => rfl
  | succ work ih => exact ih (round plan bound expected state)

theorem lanesOf_rep {rep : Rep} {key : Key} (member : key ∈ lanesOf plan bound expected rep) : key.rep = rep := by
  simp only [lanesOf, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, _, _, rfl⟩ <;> rfl

theorem events_mono {key : Key} {first second : List (family plan key).Payload}
    (included : ∀ payload ∈ first, payload ∈ second) :
    ∀ event ∈ events plan bound expected key first, event ∈ events plan bound expected key second := by
  intro event member
  cases key with
  | rule rep job =>
    simp only [events, List.mem_map, List.mem_filterMap] at member ⊢
    obtain ⟨firing, ⟨payload, found, lifted⟩, rfl⟩ := member
    exact ⟨firing, ⟨payload, included payload found, lifted⟩, rfl⟩
  | forward rep lane =>
    simp only [events, List.mem_map, List.mem_filterMap] at member ⊢
    obtain ⟨receipt, ⟨payload, found, lifted⟩, rfl⟩ := member
    exact ⟨receipt, ⟨payload, included payload found, lifted⟩, rfl⟩
  | backward rep candidate lane =>
    simp only [events, List.mem_map, List.mem_filter, List.mem_filterMap] at member ⊢
    obtain ⟨receipt, ⟨⟨payload, found, lifted⟩, same⟩, rfl⟩ := member
    exact ⟨receipt, ⟨⟨payload, included payload found, lifted⟩, same⟩, rfl⟩

theorem mem_firings {receipt : GeneralOccurrenceSemantics.Receipt} :
    ∀ {found : List Event}, receipt ∈ firings found ↔ Event.firing receipt ∈ found := by
  intro found
  induction found with
  | nil => simp [firings]
  | cons event rest ih =>
    cases event with
    | firing other => simp [firings, ih]
    | discovery pattern conversions => simp [firings, ih]

theorem addDiscoveries_prefix (born : Nat) :
    ∀ (found : List Event) (reps : List Rep), reps <+: addDiscoveries born reps found := by
  intro found
  induction found with
  | nil => intro reps; exact List.prefix_refl _
  | cons event rest ih =>
    intro reps
    cases event with
    | firing _ => exact ih reps
    | discovery pattern conversions =>
      simp only [addDiscoveries]
      split
      · exact ih reps
      · exact (List.prefix_append _ _).trans (ih _)

theorem addDiscoveries_found (born : Nat) :
    ∀ (found : List Event) (reps : List Rep) (pattern : Pattern) (conversions : List Conversion),
      Event.discovery pattern conversions ∈ found →
        ∃ rep ∈ addDiscoveries born reps found, rep.pattern = pattern := by
  intro found
  induction found with
  | nil => intro _ _ _ absent; cases absent
  | cons event rest ih =>
    intro reps pattern conversions member
    rcases List.mem_cons.mp member with same | later
    · subst same
      simp only [addDiscoveries]
      split
      · rename_i present
        obtain ⟨rep, inReps, equal⟩ := List.any_eq_true.mp present
        exact ⟨rep, (addDiscoveries_prefix born rest reps).subset inReps, by simpa using equal⟩
      · exact ⟨⟨pattern, conversions, born⟩, (addDiscoveries_prefix born rest _).subset (by simp), rfl⟩
    · cases event with
      | firing _ => exact ih reps pattern conversions later
      | discovery other otherConversions =>
        simp only [addDiscoveries]
        split
        · exact ih reps pattern conversions later
        · exact ih _ pattern conversions later

theorem addDiscoveries_extend (born : Nat) :
    ∀ (found : List Event) (reps : List Rep), ∃ tail, addDiscoveries born reps found = reps ++ tail ∧
      ∀ rep ∈ tail, rep.born = born ∧ Event.discovery rep.pattern rep.conversions ∈ found := by
  intro found
  induction found with
  | nil => intro reps; exact ⟨[], by simp [addDiscoveries], by simp⟩
  | cons event rest ih =>
    intro reps
    cases event with
    | firing receipt =>
      obtain ⟨tail, equal, fresh⟩ := ih reps
      exact ⟨tail, equal, fun rep member => ⟨(fresh rep member).1, List.mem_cons_of_mem _ (fresh rep member).2⟩⟩
    | discovery pattern conversions =>
      simp only [addDiscoveries]
      split
      · obtain ⟨tail, equal, fresh⟩ := ih reps
        exact ⟨tail, equal, fun rep member => ⟨(fresh rep member).1, List.mem_cons_of_mem _ (fresh rep member).2⟩⟩
      · obtain ⟨tail, equal, fresh⟩ := ih (reps ++ [⟨pattern, conversions, born⟩])
        refine ⟨⟨pattern, conversions, born⟩ :: tail, by rw [equal]; simp, ?_⟩
        intro rep member
        rcases List.mem_cons.mp member with rfl | later
        · exact ⟨rfl, List.mem_cons_self⟩
        · exact ⟨(fresh rep later).1, List.mem_cons_of_mem _ (fresh rep later).2⟩

theorem addDiscoveries_new (born : Nat) (found : List Event) (reps : List Rep) :
    ∀ rep ∈ (addDiscoveries born reps found).drop reps.length,
      rep.born = born ∧ Event.discovery rep.pattern rep.conversions ∈ found := by
  obtain ⟨tail, equal, fresh⟩ := addDiscoveries_extend born found reps
  rw [equal, List.drop_left]
  exact fresh

theorem events_append (key : Key) (first second : List (family plan key).Payload) :
    events plan bound expected key (first ++ second) =
      events plan bound expected key first ++ events plan bound expected key second := by
  cases key <;> simp [events, List.filterMap_append, List.filter_append]

theorem mem_lanesOf_rule {rep : Rep} {job : GeneralRuleJobs.Job} :
    Key.rule rep job ∈ lanesOf plan bound expected rep → job ∈ GeneralRuleJobs.jobs plan bound expected rep.pattern := by
  intro member
  simp only [lanesOf, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with (⟨other, present, same⟩ | ⟨_, _, impossible⟩) | ⟨_, _, _, _, impossible⟩
  · cases same; exact present
  · cases impossible
  · cases impossible

theorem mem_lanesOf_forward {rep : Rep} {lane : EquationJob.Lane} :
    Key.forward rep lane ∈ lanesOf plan bound expected rep → lane ∈ EquationJob.lanes plan bound expected rep.pattern := by
  intro member
  simp only [lanesOf, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with (⟨_, _, impossible⟩ | ⟨other, present, same⟩) | ⟨_, _, _, _, impossible⟩
  · cases impossible
  · cases same; exact present
  · cases impossible

theorem mem_lanesOf_backward {rep : Rep} {candidate : Pattern} {lane : EquationJob.Lane} :
    Key.backward rep candidate lane ∈ lanesOf plan bound expected rep →
      lane ∈ EquationJob.lanes plan bound expected candidate := by
  intro member
  simp only [lanesOf, List.mem_append, List.mem_map, List.mem_flatMap] at member
  rcases member with (⟨_, _, impossible⟩ | ⟨_, _, impossible⟩) | ⟨other, _, otherLane, present, same⟩
  · cases impossible
  · cases impossible
  · cases same; exact present

/-! ## What every reached search satisfies -/

/-- What an event says about the source. -/
def EventValid (source : Pattern) : Event → Prop
  | .firing receipt => receipt.Valid plan bound expected source
  | .discovery pattern conversions => ConversionPath plan bound expected source pattern conversions

theorem event_valid {source : Pattern} {key : Key}
    (repValid : ConversionPath plan bound expected source key.rep.pattern key.rep.conversions)
    (lane : key ∈ lanesOf plan bound expected key.rep) {payload : (family plan key).Payload}
    (valid : (family plan key).Valid payload) :
    ∀ event ∈ events plan bound expected key [payload], EventValid plan bound expected source event := by
  intro event member
  cases key with
  | rule rep job =>
    simp only [events, List.filterMap_cons, List.filterMap_nil] at member
    split at member
    · cases member
    · rename_i receipt lifted
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
      subst member
      exact ⟨repValid, Step.lift_valid plan bound expected
        ((GeneralRuleJobs.jobs_spec plan bound expected rep.pattern job).mp
          (mem_lanesOf_rule plan bound expected lane)) valid lifted⟩
  | forward rep lane' =>
    simp only [events, List.filterMap_cons, List.filterMap_nil] at member
    split at member
    · cases member
    · rename_i receipt lifted
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
      subst member
      have completion := EquationJob.lift_sound plan bound expected (mem_lanesOf_forward plan bound expected lane)
        valid lifted
      exact ConversionPath.append plan bound expected repValid (.cons completion rfl (.nil _))
  | backward rep candidate lane' =>
    simp only [events, List.filterMap_cons, List.filterMap_nil] at member
    split at member
    · cases member
    · rename_i receipt lifted
      simp only [List.filter_cons, List.filter_nil] at member
      split at member
      · rename_i same
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
        subst member
        have completion := EquationJob.lift_sound plan bound expected (mem_lanesOf_backward plan bound expected lane)
          valid lifted
        exact ConversionPath.append plan bound expected repValid (.back completion (by simpa [Key.rep] using same) (.nil _))
      · cases member

/-- An event was acted on: its receipt is published, or its member is represented. -/
def Processed (state : State plan) : Event → Prop
  | .firing receipt => receipt ∈ state.log
  | .discovery pattern _ => ∃ rep ∈ state.reps, rep.pattern = pattern

structure Reached (source : Pattern) (state : State plan) : Prop where
  valid : ∀ rep ∈ state.reps, ConversionPath plan bound expected source rep.pattern rep.conversions
  born : ∀ rep ∈ state.reps, rep.born ≤ state.round
  entries : ∀ entry ∈ state.entries, entry.1.rep ∈ state.reps ∧ entry.1 ∈ lanesOf plan bound expected entry.1.rep ∧
    entry.2 = Deep.run (family plan entry.1) (state.round - entry.1.rep.born) (Deep.start _)
  cover : ∀ rep ∈ state.reps, ∀ key ∈ lanesOf plan bound expected rep, ∃ entry ∈ state.entries, entry.1 = key
  log : ∀ receipt ∈ state.log, receipt.Valid plan bound expected source
  processed : ∀ entry ∈ state.entries, ∀ event ∈ events plan bound expected entry.1 entry.2.publication,
    Processed plan state event
  source : ∃ rep ∈ state.reps, rep.pattern = source

theorem begin_reached (source : Pattern) : Reached plan bound expected source (begin plan bound expected source) where
  valid rep member := by
    simp only [begin, List.mem_singleton] at member
    subst member
    exact .nil source
  born rep member := by simp [begin] at member; subst member; rfl
  entries entry member := by
    simp only [begin, List.mem_map] at member
    obtain ⟨key, present, rfl⟩ := member
    have same := lanesOf_rep plan bound expected present
    refine ⟨by simp [begin, same], by rw [same]; exact present, ?_⟩
    simp [begin, same, Deep.run]
  cover rep member key present := by
    simp only [begin, List.mem_singleton] at member
    subst member
    exact ⟨⟨key, Deep.start _⟩, by simp [begin, present], rfl⟩
  log receipt member := by simp [begin] at member
  processed entry member event inside := by
    simp only [begin, List.mem_map] at member
    obtain ⟨key, _, rfl⟩ := member
    simp [Deep.start, Deep.levelStart, Deep.State.publication, Deep.fresh,
      StructuralDescent.Scheduled.start] at inside
    cases key <;> simp [events] at inside
  source := ⟨⟨source, [], 0⟩, by simp [begin], rfl⟩

/-! ## A round keeps the invariant -/

/-- Everything a round has found. -/
abbrev found (state : State plan) : List Event :=
  (state.entries.map (advance plan bound expected)).flatMap Prod.snd

theorem round_round (state : State plan) : (round plan bound expected state).round = state.round + 1 := rfl

theorem round_reps (state : State plan) :
    (round plan bound expected state).reps = addDiscoveries (state.round + 1) state.reps (found plan bound expected state) :=
  rfl

theorem round_entries (state : State plan) :
    (round plan bound expected state).entries = (state.entries.map (advance plan bound expected)).map Prod.fst ++
      (((addDiscoveries (state.round + 1) state.reps (found plan bound expected state)).drop state.reps.length).flatMap
        (lanesOf plan bound expected)).map fun key => ⟨key, Deep.start (family plan key)⟩ := rfl

theorem round_log (state : State plan) :
    (round plan bound expected state).log = state.log ++ firings (found plan bound expected state) := rfl

theorem mem_events_single {key : Key} :
    ∀ {payloads : List (family plan key).Payload} {event : Event}, event ∈ events plan bound expected key payloads →
      ∃ payload ∈ payloads, event ∈ events plan bound expected key [payload] := by
  intro payloads
  induction payloads with
  | nil => intro event member; cases key <;> simp [events] at member
  | cons payload rest ih =>
    intro event member
    rw [show payload :: rest = [payload] ++ rest from rfl, events_append] at member
    rcases List.mem_append.mp member with here | later
    · exact ⟨payload, List.mem_cons_self, here⟩
    · obtain ⟨other, inside, single⟩ := ih later
      exact ⟨other, List.mem_cons_of_mem _ inside, single⟩

/-- One lane's new payloads, at its next state. -/
theorem advance_split (key : Key) (current : Deep.State (family plan key)) :
    ∃ tail, (Deep.tick (family plan key) current).publication = current.publication ++ tail ∧
      (advance plan bound expected ⟨key, current⟩).2 = events plan bound expected key tail := by
  obtain ⟨tail, grown⟩ := Deep.tick_publication_prefix (family plan key) current
  refine ⟨tail, grown.symm, ?_⟩
  simp only [advance]
  rw [← grown, List.drop_left]

theorem found_valid {source : Pattern} {state : State plan} (reached : Reached plan bound expected source state) :
    ∀ event ∈ found plan bound expected state, EventValid plan bound expected source event := by
  intro event member
  simp only [found, List.flatMap_map, List.mem_flatMap] at member
  obtain ⟨⟨key, current⟩, present, inEvents⟩ := member
  obtain ⟨repMember, lane, currentEq⟩ := reached.entries ⟨key, current⟩ present
  simp only at repMember lane currentEq
  obtain ⟨tail, grown, split⟩ := advance_split plan bound expected key current
  rw [split] at inEvents
  obtain ⟨payload, inTail, single⟩ := mem_events_single plan bound expected inEvents
  have published : payload ∈ (Deep.run (family plan key) (state.round - key.rep.born + 1)
      (Deep.start _)).publication := by
    rw [Deep.run_succ, ← currentEq, grown]
    exact List.mem_append_right _ inTail
  exact event_valid plan bound expected (reached.valid _ repMember) lane
    (Deep.sound (family plan key) _ payload published) event single

theorem processed_mono {state : State plan} {event : Event} (done : Processed plan state event) :
    Processed plan (round plan bound expected state) event := by
  cases event with
  | firing receipt =>
    exact (show receipt ∈ state.log ++ _ from List.mem_append_left _ done)
  | discovery pattern conversions =>
    obtain ⟨rep, member, same⟩ := done
    exact ⟨rep, by rw [round_reps]; exact (addDiscoveries_prefix _ _ _).subset member, same⟩

theorem processed_found {state : State plan} {event : Event} (member : event ∈ found plan bound expected state) :
    Processed plan (round plan bound expected state) event := by
  cases event with
  | firing receipt =>
    change receipt ∈ state.log ++ firings (found plan bound expected state)
    exact List.mem_append_right _ (mem_firings.mpr member)
  | discovery pattern conversions =>
    rw [Processed, round_reps]
    exact addDiscoveries_found _ _ _ _ _ member

theorem round_reached {source : Pattern} {state : State plan} (reached : Reached plan bound expected source state) :
    Reached plan bound expected source (round plan bound expected state) := by
  obtain ⟨tail, extended, fresh⟩ := addDiscoveries_extend (state.round + 1) (found plan bound expected state) state.reps
  have repsEq : (round plan bound expected state).reps = state.reps ++ tail := by rw [round_reps, extended]
  have dropEq : (addDiscoveries (state.round + 1) state.reps (found plan bound expected state)).drop state.reps.length =
      tail := by rw [extended, List.drop_left]
  have memReps : ∀ rep, rep ∈ (round plan bound expected state).reps ↔ rep ∈ state.reps ∨ rep ∈ tail := by
    intro rep; rw [repsEq, List.mem_append]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rep member
    rcases (memReps rep).mp member with old | new
    · exact reached.valid rep old
    · exact found_valid plan bound expected reached _ (fresh rep new).2
  · intro rep member
    rw [round_round]
    rcases (memReps rep).mp member with old | new
    · exact Nat.le_succ_of_le (reached.born rep old)
    · exact Nat.le_of_eq (fresh rep new).1
  · intro entry' member
    rw [round_entries, dropEq] at member
    rcases List.mem_append.mp member with advanced | started
    · simp only [List.map_map, List.mem_map] at advanced
      obtain ⟨⟨key, current⟩, present, rfl⟩ := advanced
      obtain ⟨repMember, lane, currentEq⟩ := reached.entries ⟨key, current⟩ present
      simp only at repMember lane currentEq
      have bornBound := reached.born _ repMember
      refine ⟨(memReps _).mpr (.inl repMember), lane, ?_⟩
      simp only [Function.comp, advance, round_round]
      rw [currentEq, ← Deep.run_succ]
      congr 1
      omega
    · obtain ⟨key, inLanes, rfl⟩ := List.mem_map.mp started
      obtain ⟨rep, inTail, inRep⟩ := List.mem_flatMap.mp inLanes
      have same := lanesOf_rep plan bound expected inRep
      refine ⟨by rw [same]; exact (memReps rep).mpr (.inr inTail), by rw [same]; exact inRep, ?_⟩
      simp only [round_round, same, (fresh rep inTail).1, Nat.sub_self]
      rfl
  · intro rep member key inLanes
    rw [round_entries, dropEq]
    rcases (memReps rep).mp member with old | new
    · obtain ⟨entry, present, same⟩ := reached.cover rep old key inLanes
      exact ⟨(advance plan bound expected entry).1, List.mem_append_left _
        (List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨entry, present, rfl⟩, rfl⟩), by simp [advance, same]⟩
    · exact ⟨⟨key, Deep.start _⟩, List.mem_append_right _
        (List.mem_map.mpr ⟨key, List.mem_flatMap.mpr ⟨rep, new, inLanes⟩, rfl⟩), rfl⟩
  · intro receipt member
    rw [round_log] at member
    rcases List.mem_append.mp member with old | new
    · exact reached.log receipt old
    · exact found_valid plan bound expected reached _ (mem_firings.mp new)
  · intro entry' member event inside
    rw [round_entries, dropEq] at member
    rcases List.mem_append.mp member with advanced | started
    · simp only [List.map_map, List.mem_map] at advanced
      obtain ⟨⟨key, current⟩, present, rfl⟩ := advanced
      obtain ⟨tail', grown, split⟩ := advance_split plan bound expected key current
      simp only [Function.comp, advance] at inside
      rw [grown, events_append] at inside
      rcases List.mem_append.mp inside with old | new
      · exact processed_mono plan bound expected (reached.processed ⟨key, current⟩ present event old)
      · apply processed_found plan bound expected
        simp only [found, List.flatMap_map, List.mem_flatMap]
        exact ⟨⟨key, current⟩, present, by rw [split]; exact new⟩
    · obtain ⟨key, _, rfl⟩ := List.mem_map.mp started
      simp [Deep.start, Deep.levelStart, Deep.State.publication, Deep.fresh,
        StructuralDescent.Scheduled.start] at inside
      cases key <;> simp [events] at inside
  · obtain ⟨rep, member, same⟩ := reached.source
    exact ⟨rep, (memReps rep).mpr (.inl member), same⟩

theorem rounds_reached (source : Pattern) (work : Nat) :
    Reached plan bound expected source (rounds plan bound expected work (begin plan bound expected source)) := by
  induction work with
  | zero => exact begin_reached plan bound expected source
  | succ work ih => rw [rounds_succ]; exact round_reached plan bound expected ih

/-! ## Completeness in the limit -/

section Search

variable (source : Pattern)

/-- The search after some rounds. -/
abbrev runAt (work : Nat) : State plan := rounds plan bound expected work (begin plan bound expected source)

theorem runAt_round (work : Nat) : (runAt plan bound expected source work).round = work := by
  induction work with
  | zero => rfl
  | succ work ih => simp only [runAt, rounds_succ, round_round]; simp only [runAt] at ih; rw [ih]

theorem runAt_reps_mono (work extra : Nat) :
    ∀ rep ∈ (runAt plan bound expected source work).reps, rep ∈ (runAt plan bound expected source (work + extra)).reps := by
  induction extra with
  | zero => intro rep member; exact member
  | succ extra ih =>
    intro rep member
    simp only [runAt, ← Nat.add_assoc, rounds_succ, round_reps]
    exact (addDiscoveries_prefix _ _ _).subset (ih rep member)

/-- **A lane's published payload is acted on**, a bounded number of rounds after its member was
found. -/
theorem eventually_processed {work : Nat} {rep : Rep} (member : rep ∈ (runAt plan bound expected source work).reps)
    {key : Key} (inLanes : key ∈ lanesOf plan bound expected rep) {payload : (family plan key).Payload} {extra : Nat}
    (published : payload ∈ (Deep.run (family plan key) extra (Deep.start _)).publication) :
    ∀ event ∈ events plan bound expected key [payload],
      Processed plan (runAt plan bound expected source (work + extra)) event := by
  intro event inside
  have reached := rounds_reached plan bound expected source (work + extra)
  have later := runAt_reps_mono plan bound expected source work extra rep member
  obtain ⟨⟨key', current⟩, present, same⟩ := reached.cover rep later key inLanes
  simp only at same
  subst same
  obtain ⟨_, _, currentEq⟩ := reached.entries ⟨key', current⟩ present
  simp only at currentEq
  have repSame := lanesOf_rep plan bound expected inLanes
  have bornBound := (rounds_reached plan bound expected source work).born rep member
  rw [runAt_round] at bornBound
  have enough : extra ≤ (runAt plan bound expected source (work + extra)).round - key'.rep.born := by
    rw [runAt_round, repSame]; omega
  obtain ⟨more, total⟩ := Nat.exists_eq_add_of_le enough
  have grown := Deep.run_publication_prefix (family plan key') more
    (Deep.run (family plan key') extra (Deep.start _))
  rw [← Deep.run_add, ← total, ← currentEq] at grown
  apply reached.processed ⟨key', current⟩ present event
  exact events_mono plan bound expected (fun other single => by
    simp only [List.mem_singleton] at single
    subst single
    exact grown.subset published) event inside

/-- A member is found after finitely many rounds. -/
def Visited (pattern : Pattern) : Prop :=
  ∃ work, ∃ rep ∈ (runAt plan bound expected source work).reps, rep.pattern = pattern

theorem visited_source : Visited plan bound expected source source := by
  obtain ⟨rep, member, same⟩ := (rounds_reached plan bound expected source 0).source
  exact ⟨0, rep, member, same⟩

theorem visited_forward {from_ : Pattern} (visited : Visited plan bound expected source from_)
    {receipt : GeneralEquationJobs.Receipt}
    (completion : GeneralEquationJobs.Completion plan bound expected from_ receipt) :
    Visited plan bound expected source receipt.target := by
  obtain ⟨work, rep, member, rfl⟩ := visited
  obtain ⟨present, valid, lifted⟩ := EquationJob.lane_of_completion plan bound expected completion
  have inLanes : Key.forward rep ⟨receipt.job, ⟨receipt.captured, receipt.matcherTrace⟩⟩ ∈ lanesOf plan bound expected rep := by
    simp only [lanesOf, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨_, present, rfl⟩)
  obtain ⟨extra, published⟩ := Deep.complete_in_limit (family plan (Key.forward rep _)) valid
  have done := eventually_processed plan bound expected source member inLanes published
    (.discovery receipt.target (rep.conversions ++ [.forward receipt])) (by simp [events, lifted])
  obtain ⟨found, inReps, same⟩ := done
  exact ⟨work + extra, found, inReps, same⟩

theorem visited_backward (checked : Predecessors.equationsChecked plan = true)
    {into : Pattern} (visited : Visited plan bound expected source into)
    {from_ : Pattern} {receipt : GeneralEquationJobs.Receipt}
    (completion : GeneralEquationJobs.Completion plan bound expected from_ receipt) (endpoint : receipt.target = into) :
    Visited plan bound expected source from_ := by
  obtain ⟨work, rep, member, rfl⟩ := visited
  have candidate : from_ ∈ Predecessors.predecessors plan bound rep.pattern := by
    rw [← endpoint]
    exact Predecessors.mem_predecessors checked completion
  obtain ⟨present, valid, lifted⟩ := EquationJob.lane_of_completion plan bound expected completion
  have inLanes : Key.backward rep from_ ⟨receipt.job, ⟨receipt.captured, receipt.matcherTrace⟩⟩ ∈
      lanesOf plan bound expected rep := by
    simp only [lanesOf, List.mem_append, List.mem_map, List.mem_flatMap]
    exact Or.inr ⟨from_, candidate, _, present, rfl⟩
  obtain ⟨extra, published⟩ := Deep.complete_in_limit (family plan (Key.backward rep from_ _)) valid
  have done := eventually_processed plan bound expected source member inLanes published
    (.discovery from_ (rep.conversions ++ [.reverse receipt])) (by simp [events, lifted, endpoint])
  obtain ⟨found, inReps, same⟩ := done
  exact ⟨work + extra, found, inReps, same⟩

/-- **Every member of the source's equality class is found.** -/
theorem visited_of_equivalent (checked : Predecessors.equationsChecked plan = true)
    {member : Pattern}
    (equivalent : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) source member) :
    Visited plan bound expected source member := by
  suffices both : ∀ first second, Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) first second →
      (Visited plan bound expected source first ↔ Visited plan bound expected source second) from
    (both source member equivalent).mp (visited_source plan bound expected source)
  intro first second related
  induction related with
  | rel first second step =>
    obtain ⟨receipt, completion, endpoint⟩ := step
    exact ⟨fun visited => endpoint ▸ visited_forward plan bound expected source visited completion,
      fun visited => visited_backward plan bound expected source checked visited completion endpoint⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- A firing at a found member is published. -/
theorem fired_at_visited {pattern : Pattern} (visited : Visited plan bound expected source pattern)
    {receipt : GeneralRuleJobs.Receipt} (valid : receipt.Valid plan bound expected pattern) :
    ∃ work, ∃ published ∈ (runAt plan bound expected source work).log,
      published.representative = pattern ∧ published.firing = receipt := by
  obtain ⟨work, rep, member, rfl⟩ := visited
  obtain ⟨fired, lifted⟩ := Step.lift_of_valid plan bound expected valid
  have inLanes : Key.rule rep receipt.job ∈ lanesOf plan bound expected rep := by
    simp only [lanesOf, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl ⟨_, (GeneralRuleJobs.jobs_spec plan bound expected rep.pattern receipt.job).mpr valid.1, rfl⟩)
  obtain ⟨extra, published⟩ := DeepRoot.complete_in_limit fired
  have done := eventually_processed plan bound expected source member inLanes (key := Key.rule rep receipt.job)
    (payload := Step.firingOf receipt) published
    (.firing ⟨rep.pattern, rep.conversions, receipt⟩) (by simp [events, lifted])
  exact ⟨work + extra, _, done, rfl, rfl⟩

/-- **Sound.** Every published receipt is a valid step receipt at the source. -/
theorem sound (work : Nat) :
    ∀ receipt ∈ (runAt plan bound expected source work).log, receipt.Valid plan bound expected source :=
  (rounds_reached plan bound expected source work).log

/-- **Complete in the limit.** Every step of the plan's GSLT from the source is published after
finitely many rounds, up to equality of the target, when the plan's equations are balanced
(every accepted compiled plan: `Predecessors.equationsChecked_of_complete`). -/
theorem complete_in_limit (checked : Predecessors.equationsChecked plan = true) {target : Pattern}
    (step : (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target) :
    ∃ work, ∃ receipt ∈ (runAt plan bound expected source work).log,
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) receipt.target target := by
  obtain ⟨representative, receipt, before, valid, after⟩ := step
  obtain ⟨work, published, member, _, same⟩ := fired_at_visited plan bound expected source
    (visited_of_equivalent plan bound expected source checked before) valid
  exact ⟨work, published, member, by simpa [GeneralOccurrenceSemantics.Receipt.target, same] using after⟩

end Search

/-! ## Complete searches are exact -/

section Exact

variable (source : Pattern) (work : Nat)

/-- In a complete search, every valid payload of every lane has been acted on. -/
theorem processed_of_complete (done : complete plan (runAt plan bound expected source work) = true)
    {rep : Rep} (member : rep ∈ (runAt plan bound expected source work).reps)
    {key : Key} (inLanes : key ∈ lanesOf plan bound expected rep) {payload : (family plan key).Payload}
    (valid : (family plan key).Valid payload) :
    ∀ event ∈ events plan bound expected key [payload], Processed plan (runAt plan bound expected source work) event := by
  intro event inside
  have reached := rounds_reached plan bound expected source work
  obtain ⟨⟨key', current⟩, present, same⟩ := reached.cover rep member key inLanes
  simp only at same
  subst same
  obtain ⟨_, _, currentEq⟩ := reached.entries ⟨key', current⟩ present
  simp only at currentEq
  have certified : current.complete = true := List.all_eq_true.mp done ⟨key', current⟩ present
  rw [currentEq] at certified
  have published := Deep.exact_of_complete (family plan key') _ certified valid
  rw [← currentEq] at published
  apply reached.processed ⟨key', current⟩ present event
  exact events_mono plan bound expected (fun other single => by
    simp only [List.mem_singleton] at single
    subst single
    exact published) event inside

/-- A member represented in the search now. -/
def Represented (pattern : Pattern) : Prop :=
  ∃ rep ∈ (runAt plan bound expected source work).reps, rep.pattern = pattern

theorem represented_closed (checked : Predecessors.equationsChecked plan = true)
    (done : complete plan (runAt plan bound expected source work) = true) {first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) first second) :
    Represented plan bound expected source work first ↔ Represented plan bound expected source work second := by
  induction related with
  | rel first second step =>
    obtain ⟨receipt, completion, endpoint⟩ := step
    obtain ⟨present, valid, lifted⟩ := EquationJob.lane_of_completion plan bound expected completion
    constructor
    · rintro ⟨rep, member, rfl⟩
      have inLanes : Key.forward rep ⟨receipt.job, ⟨receipt.captured, receipt.matcherTrace⟩⟩ ∈
          lanesOf plan bound expected rep := by
        simp only [lanesOf, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨_, present, rfl⟩)
      obtain ⟨found, inReps, same⟩ := processed_of_complete plan bound expected source work done member inLanes valid
        (.discovery receipt.target (rep.conversions ++ [.forward receipt])) (by simp [events, lifted])
      exact ⟨found, inReps, same.trans endpoint⟩
    · rintro ⟨rep, member, rfl⟩
      have candidate : first ∈ Predecessors.predecessors plan bound rep.pattern := by
        rw [← endpoint]
        exact Predecessors.mem_predecessors checked completion
      have inLanes : Key.backward rep first ⟨receipt.job, ⟨receipt.captured, receipt.matcherTrace⟩⟩ ∈
          lanesOf plan bound expected rep := by
        simp only [lanesOf, List.mem_append, List.mem_map, List.mem_flatMap]
        exact Or.inr ⟨first, candidate, _, present, rfl⟩
      exact processed_of_complete plan bound expected source work done member inLanes valid
        (.discovery first (rep.conversions ++ [.reverse receipt])) (by simp [events, lifted, endpoint])
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ first second => exact first.trans second

/-- **A complete search is exact.** Once every lane is certified, every step of the plan's GSLT
from the source is published, up to equality of the target. -/
theorem exact_of_complete (checked : Predecessors.equationsChecked plan = true)
    (done : complete plan (runAt plan bound expected source work) = true) {target : Pattern}
    (step : (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target) :
    ∃ receipt ∈ (runAt plan bound expected source work).log,
      Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan bound expected) receipt.target target := by
  obtain ⟨representative, receipt, before, valid, after⟩ := step
  have here : Represented plan bound expected source work source := (rounds_reached plan bound expected source work).source
  obtain ⟨rep, member, rfl⟩ := (represented_closed plan bound expected source work checked done before).mp here
  obtain ⟨fired, lifted⟩ := Step.lift_of_valid plan bound expected valid
  have inLanes : Key.rule rep receipt.job ∈ lanesOf plan bound expected rep := by
    simp only [lanesOf, List.mem_append, List.mem_map]
    exact Or.inl (Or.inl ⟨_, (GeneralRuleJobs.jobs_spec plan bound expected rep.pattern receipt.job).mpr valid.1, rfl⟩)
  have published := processed_of_complete plan bound expected source work done member inLanes (key := Key.rule rep receipt.job)
    (payload := Step.firingOf receipt) fired (.firing ⟨rep.pattern, rep.conversions, receipt⟩) (by simp [events, lifted])
  exact ⟨_, published, by simpa [GeneralOccurrenceSemantics.Receipt.target] using after⟩

end Exact

/-! ## The search and its runner -/

/-- Complete when every lane is certified; otherwise pending. -/
def status (state : State plan) : Mettapedia.Machines.ResumableSearchRunner.Status :=
  if complete plan state then .complete else .pending

/-- Steps modulo equations as a resumable search. -/
def search : Mettapedia.Machines.ResumableSearchRunner.Search Pattern (State plan) GeneralOccurrenceSemantics.Receipt where
  run source work := rounds plan bound expected work (begin plan bound expected source)
  resume state work := rounds plan bound expected work state
  publication := State.log
  status := status plan
  target := GeneralOccurrenceSemantics.Receipt.target
  Valid source receipt := receipt.Valid plan bound expected source

theorem rounds_add (first second : Nat) (state : State plan) :
    rounds plan bound expected (first + second) state =
      rounds plan bound expected second (rounds plan bound expected first state) := by
  induction first generalizing state with
  | zero => simp [rounds]
  | succ first ih => simpa only [Nat.succ_add, rounds] using ih (round plan bound expected state)

theorem rounds_log_prefix (work : Nat) (state : State plan) :
    state.log <+: (rounds plan bound expected work state).log := by
  induction work generalizing state with
  | zero => exact List.prefix_refl _
  | succ work ih => exact (List.prefix_append _ _).trans (ih (round plan bound expected state))

theorem search_lawful : (search plan bound expected).Lawful where
  resume_run source first extra := (rounds_add plan bound expected first extra _).symm
  publication_prefix source first extra := by
    change (rounds plan bound expected first _).log <+: (rounds plan bound expected (first + extra) _).log
    rw [rounds_add]
    exact rounds_log_prefix plan bound expected extra _
  sound source work receipt member := sound plan bound expected source work receipt member

/-- A complete search with an empty publication leaves no step. -/
theorem no_step_of_complete (checked : Predecessors.equationsChecked plan = true)
    (source : Pattern) (work : Nat)
    (finished : (search plan bound expected).status ((search plan bound expected).run source work) = .complete)
    (published : (search plan bound expected).publication ((search plan bound expected).run source work) = []) :
    ∀ target, ¬ (GeneralOccurrenceSemantics.gslt plan bound expected).Step source target := by
  intro target step
  have done : complete plan (runAt plan bound expected source work) = true := by
    change (if complete plan (runAt plan bound expected source work) then _ else _) = _ at finished
    split at finished
    · assumption
    · cases finished
  obtain ⟨receipt, member, _⟩ := exact_of_complete plan bound expected source work checked done step
  change (runAt plan bound expected source work).log = [] at published
  rw [published] at member
  cases member

/-- A machine of the runner over steps modulo equations. -/
abbrev Machine := Mettapedia.Machines.ResumableSearchRunner.Machine Pattern (State plan) GeneralOccurrenceSemantics.Receipt

/-- **Every run is a reduction sequence** of the plan's GSLT, modulo its equations. -/
theorem run_chain (source : Pattern) (ticks quantum : Nat) :
    let machine := Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search plan bound expected) ticks quantum
      (Mettapedia.Machines.ResumableSearchRunner.Machine.begin (search plan bound expected) source)
    machine.states.reverse.head? = some source ∧
      machine.states.reverse.IsChain (GeneralOccurrenceSemantics.gslt plan bound expected).Step :=
  Mettapedia.Machines.ResumableSearchRunner.run_chain (search_lawful plan bound expected)
    (fun valid => GeneralOccurrenceSemantics.Receipt.semantic_step plan bound expected valid) source ticks quantum

/-- **A normal ending is exact**: a reached machine that is done has no step at its state. -/
theorem done_no_step (checked : Predecessors.equationsChecked plan = true)
    {machine : Machine plan}
    (reached : Mettapedia.Machines.ResumableSearchRunner.Reached (search plan bound expected) machine)
    (done : machine.phase = .done) :
    ∀ target, ¬ (GeneralOccurrenceSemantics.gslt plan bound expected).Step machine.state target :=
  Mettapedia.Machines.ResumableSearchRunner.done_no_step (no_step_of_complete plan bound expected checked)
    reached done

end Mettapedia.OSLF.MeTTaIL.Complete.Classes
