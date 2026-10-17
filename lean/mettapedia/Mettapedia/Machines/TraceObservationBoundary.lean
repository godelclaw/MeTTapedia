import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis
import Mettapedia.Machines.RunObservation
import Mettapedia.Algebra.WorkSpan
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Relation

/-!
# Trace observation boundaries

A replay checker can validate only information that an execution trace
actually exports.  This module isolates three erasures that occur at common
native trace boundaries:

* flattening a causal receipt retains event occurrences but forgets edges;
* exporting an observation without its demand annotation forgets both the
  demand role and expected type;
* reporting an external interruption without its frontier forgets the live
  states that remained when execution stopped.

The counterexamples below are constructive non-injectivity results.  They
prevent a checker from reconstructing any of these witnesses solely from the
corresponding erased observation.
-/

namespace Mettapedia.Machines

/-! ## Causal edges -/

universe uCausal

/-- One event occurrence together with its immediate causal predecessors. -/
structure CausalEvent (Event : Type uCausal) where
  event : Event
  directCauses : List Event
deriving DecidableEq, Repr

/-- A finite causal receipt.  Roots identify the events directly supporting
the published observation; `events` retains the immediate-edge relation. -/
structure CausalReceipt (Event : Type uCausal) where
  roots : List Event
  events : List (CausalEvent Event)
deriving DecidableEq, Repr

namespace CausalReceipt

variable {Event : Type uCausal}

/-- The occurrence-preserving support currently visible to a flattened trace.
The order and multiplicity of event occurrences survive; causal edges do not. -/
def flattenedSupport (receipt : CausalReceipt Event) : List Event :=
  receipt.events.map CausalEvent.event

/-- Boundary identities describe dependencies captured before recording
began. They are visible references, not a reconstructed earlier history. -/
def known (boundary : List Event) (receipt : CausalReceipt Event) : List Event :=
  boundary ++ receipt.flattenedSupport

/-- An event is fresh and refers only to earlier available occurrences.
Repeated predecessor slots remain repeated slots. -/
def Ordered (available : List Event) : List (CausalEvent Event) → Prop
  | [] => True
  | event :: rest => event.event ∉ available ∧
      (∀ cause ∈ event.directCauses, cause ∈ available) ∧
      Ordered (available ++ [event.event]) rest

def WellFormed (boundary : List Event) (receipt : CausalReceipt Event) : Prop :=
  boundary.Nodup ∧ Ordered boundary receipt.events ∧
    ∀ root ∈ receipt.roots, root ∈ receipt.known boundary

def checkEvents [DecidableEq Event] (available : List Event) : List (CausalEvent Event) → Bool
  | [] => true
  | event :: rest => decide (event.event ∉ available) &&
      event.directCauses.all (fun cause => decide (cause ∈ available)) &&
      checkEvents (available ++ [event.event]) rest

def check [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event) : Bool :=
  decide boundary.Nodup && checkEvents boundary receipt.events &&
    receipt.roots.all (fun root => decide (root ∈ receipt.known boundary))

theorem checkEvents_iff [DecidableEq Event] (available : List Event)
    (events : List (CausalEvent Event)) :
    checkEvents available events = true ↔ Ordered available events := by
  induction events generalizing available with
  | nil => simp [checkEvents, Ordered]
  | cons event rest ih => simp [checkEvents, Ordered, ih, and_assoc]

theorem check_iff [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event) :
    check boundary receipt = true ↔ WellFormed boundary receipt := by
  simp [check, WellFormed, checkEvents_iff, and_assoc]

theorem ordered_append (available : List Event) (first second : List (CausalEvent Event)) :
    Ordered available (first ++ second) ↔
      Ordered available first ∧ Ordered (available ++ first.map CausalEvent.event) second := by
  induction first generalizing available with
  | nil => simp [Ordered]
  | cons event rest ih => simp [Ordered, ih, List.append_assoc, and_assoc]

theorem ordered_distinct (available : List Event) (events : List (CausalEvent Event))
    (distinct : available.Nodup) (ordered : Ordered available events) :
    (available ++ events.map CausalEvent.event).Nodup := by
  induction events generalizing available with
  | nil => simpa using distinct
  | cons event rest ih =>
    rcases ordered with ⟨fresh, _, tail⟩
    have extended : (available ++ [event.event]).Nodup := by
      simp only [List.nodup_append, distinct, List.nodup_cons, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_self, true_and, List.mem_singleton]
      rintro member present other rfl rfl
      exact fresh present
    simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
      ih (available ++ [event.event]) extended tail

/-- Every retained cause has a strictly smaller chronological rank. -/
theorem ordered_rank [DecidableEq Event] (available : List Event)
    (events : List (CausalEvent Event)) (ordered : Ordered available events)
    (event : CausalEvent Event) (present : event ∈ events)
    (cause : Event) (depends : cause ∈ event.directCauses) :
    (available ++ events.map CausalEvent.event).idxOf cause <
      (available ++ events.map CausalEvent.event).idxOf event.event := by
  induction events generalizing available with
  | nil => cases present
  | cons head rest ih =>
    rcases ordered with ⟨fresh, causes, tail⟩
    rcases List.mem_cons.mp present with equal | member
    · subst event
      rw [List.map_cons, List.idxOf_append_of_mem (causes cause depends),
        List.idxOf_append_of_notMem fresh]
      simpa using List.idxOf_lt_length_of_mem (causes cause depends)
    · simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
        ih (available ++ [head.event]) tail member

def Direct (receipt : CausalReceipt Event) (cause effect : Event) : Prop :=
  ∃ event ∈ receipt.events, event.event = effect ∧ cause ∈ event.directCauses

theorem direct_rank [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (valid : WellFormed boundary receipt) {cause effect : Event}
    (edge : receipt.Direct cause effect) :
    (receipt.known boundary).idxOf cause < (receipt.known boundary).idxOf effect := by
  obtain ⟨event, present, rfl, depends⟩ := edge
  exact ordered_rank boundary receipt.events valid.2.1 event present cause depends

theorem ancestry_rank [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (valid : WellFormed boundary receipt) {cause effect : Event}
    (path : Relation.TransGen receipt.Direct cause effect) :
    (receipt.known boundary).idxOf cause < (receipt.known boundary).idxOf effect := by
  induction path with
  | single edge => exact direct_rank boundary receipt valid edge
  | tail path edge ih => exact ih.trans (direct_rank boundary receipt valid edge)

theorem no_causal_cycle [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (valid : WellFormed boundary receipt) (event : Event) :
    ¬ Relation.TransGen receipt.Direct event event := by
  intro cycle
  exact Nat.lt_irrefl _ (ancestry_rank boundary receipt valid cycle)

/-- Append one already-identified event. Rejected input leaves the original
immutable receipt available to its caller. This checks structure, not whether
the evaluator actually produced all of the stated dependency edges. -/
def appendEvent? [DecidableEq Event] (boundary : List Event) (receipt : CausalReceipt Event)
    (event : CausalEvent Event) : Option (CausalReceipt Event) :=
  if event.event ∉ receipt.known boundary ∧
      ∀ cause ∈ event.directCauses, cause ∈ receipt.known boundary then
    some { receipt with events := receipt.events ++ [event] }
  else none

theorem appendEvent?_valid [DecidableEq Event] (boundary : List Event)
    (receipt result : CausalReceipt Event) (event : CausalEvent Event)
    (valid : WellFormed boundary receipt) (accepted : appendEvent? boundary receipt event = some result) :
    WellFormed boundary result := by
  unfold appendEvent? at accepted
  split at accepted
  · rename_i allowed
    cases Option.some.inj accepted
    refine ⟨valid.1, ?_, ?_⟩
    · apply (ordered_append boundary receipt.events [event]).mpr
      exact ⟨valid.2.1, allowed.1, allowed.2, trivial⟩
    · intro root present
      have old := valid.2.2 root present
      simpa only [known, flattenedSupport, List.map_append, List.map_cons,
        List.map_nil, List.append_assoc] using
        (List.mem_append_left [event.event] old)
  · cases accepted

/-- Query the retained immediate predecessors of one occurrence. A missing
node returns `none`; an observed root with no predecessors returns `some []`. -/
def causes? [DecidableEq Event] (receipt : CausalReceipt Event) (identity : Event) :
    Option (List Event) :=
  (receipt.events.find? (fun event => decide (event.event = identity))).map CausalEvent.directCauses

theorem causes?_sound [DecidableEq Event] (receipt : CausalReceipt Event)
    (identity : Event) (causes : List Event) (found : receipt.causes? identity = some causes) :
    ∃ event ∈ receipt.events, event.event = identity ∧ event.directCauses = causes := by
  obtain ⟨event, selected, same⟩ := Option.map_eq_some_iff.mp found
  exact ⟨event, List.mem_of_find?_eq_some selected,
    of_decide_eq_true (List.find?_some
      (p := fun candidate : CausalEvent Event => decide (candidate.event = identity)) selected), same⟩

namespace Controls

def shared : CausalReceipt Nat :=
  ⟨[2, 3], [⟨1, []⟩, ⟨2, [1]⟩, ⟨3, [1]⟩]⟩

def erasedSharing : CausalReceipt Nat :=
  ⟨[2, 3], [⟨1, []⟩, ⟨2, [1]⟩, ⟨3, []⟩]⟩

theorem shared_production_distinct_uses :
    check [] shared = true ∧ shared.flattenedSupport = [1, 2, 3] ∧
      shared.causes? 2 = some [1] ∧ shared.causes? 3 = some [1] := by
  decide

theorem missing_occurrence_differs_from_empty_causes :
    shared.causes? 0 = none ∧ shared.causes? 1 = some [] := by decide

theorem missing_dependency_refused : check [] (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat) = false := by
  decide

theorem captured_boundary_is_explicit :
    check [9] (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat) = true := by decide

theorem duplicated_identity_refused :
    check [] (⟨[1], [⟨1, []⟩, ⟨1, []⟩]⟩ : CausalReceipt Nat) = false := by decide

theorem cycle_refused :
    check [] (⟨[2], [⟨1, [2]⟩, ⟨2, [1]⟩]⟩ : CausalReceipt Nat) = false := by decide

/-- A structurally valid graph can omit a real semantic dependency. Native
event correspondence is required in addition to this structural checker. -/
theorem valid_structure_does_not_authenticate_edges :
    check [] shared = true ∧ check [] erasedSharing = true ∧
      shared.flattenedSupport = erasedSharing.flattenedSupport ∧
      shared.causes? 3 ≠ erasedSharing.causes? 3 := by
  decide

end Controls

/-! ## Retained transitive ancestry

The query reuses the finite catalogue sweep. Its answer describes only the
represented graph, with captured boundary identities included explicitly.
A structurally checked receipt does not authenticate native dependency edges.
-/

/-- Immediate dependants of an occurrence, in retained recording order. -/
def dependants [DecidableEq Event] (receipt : CausalReceipt Event)
    (identity : Event) : List Event :=
  (receipt.events.filter (fun event => decide (identity ∈ event.directCauses))).map CausalEvent.event

theorem mem_dependants [DecidableEq Event] (receipt : CausalReceipt Event)
    (cause effect : Event) : effect ∈ receipt.dependants cause ↔ receipt.Direct cause effect := by
  simp only [dependants, List.mem_map, List.mem_filter, decide_eq_true_eq, Direct]
  constructor
  · rintro ⟨event, ⟨present, depends⟩, same⟩
    exact ⟨event, present, same, depends⟩
  · rintro ⟨event, present, same, depends⟩
    exact ⟨event, ⟨present, depends⟩, same⟩

/-- Both endpoints of a retained edge are available in its declared boundary. -/
theorem direct_known [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (valid : WellFormed boundary receipt)
    {cause effect : Event} (edge : receipt.Direct cause effect) :
    cause ∈ receipt.known boundary ∧ effect ∈ receipt.known boundary := by
  have effectKnown : effect ∈ receipt.known boundary := by
    obtain ⟨event, present, rfl, _⟩ := edge
    exact List.mem_append_right _ (List.mem_map.mpr ⟨event, present, rfl⟩)
  exact ⟨List.idxOf_lt_length_iff.mp
    ((direct_rank boundary receipt valid edge).trans (List.idxOf_lt_length_iff.mpr effectKnown)),
    effectKnown⟩

/-- Reverse dependencies let the existing affected-item sweep answer which
recorded occurrences support a selected occurrence. -/
def dependencyCatalogue [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) :
    Mettapedia.Algorithms.WellFoundedServices.Catalogue Event where
  items := receipt.known boundary
  deps := receipt.dependants

theorem catalogue_uses_iff [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (valid : WellFormed boundary receipt)
    (cause effect : Event) :
    (receipt.dependencyCatalogue boundary).Uses cause effect ↔ receipt.Direct cause effect := by
  change cause ∈ receipt.known boundary ∧ effect ∈ receipt.dependants cause ↔ _
  rw [mem_dependants]
  exact ⟨And.right, fun edge => ⟨(direct_known boundary receipt valid edge).1, edge⟩⟩

/-- Missing queried occurrences and invalid receipt structure refuse the
readout. Equal payloads are irrelevant: the query uses occurrence identities.
The result includes the selected occurrence and captured boundary references;
it makes no claim about unavailable history preceding those references. -/
def ancestors? [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (identity : Event) : Option (List Event) :=
  if receipt.check boundary = true ∧ identity ∈ receipt.known boundary then
    some ((receipt.dependencyCatalogue boundary).affected [identity])
  else none

theorem ancestors?_refused [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (identity : Event)
    (missing : identity ∉ receipt.known boundary) :
    receipt.ancestors? boundary identity = none := by
  simp [ancestors?, missing]

theorem ancestors?_exact [DecidableEq Event] (boundary : List Event)
    (receipt : CausalReceipt Event) (identity : Event) (result : List Event)
    (reported : receipt.ancestors? boundary identity = some result) :
    WellFormed boundary receipt ∧ identity ∈ receipt.known boundary ∧
      ∀ cause, cause ∈ result ↔ cause = identity ∨ Relation.TransGen receipt.Direct cause identity := by
  unfold ancestors? at reported
  split at reported
  · rename_i admitted
    have valid := (check_iff boundary receipt).mp admitted.1
    cases Option.some.inj reported
    refine ⟨valid, admitted.2, ?_⟩
    intro cause
    rw [(receipt.dependencyCatalogue boundary).mem_affected [identity] cause]
    simp only [List.mem_singleton, exists_eq_left]
    have same : Relation.ReflTransGen (receipt.dependencyCatalogue boundary).Uses cause identity ↔
        Relation.ReflTransGen receipt.Direct cause identity := by
      constructor
      · intro path
        exact Relation.ReflTransGen.mono (fun left right edge =>
          (catalogue_uses_iff boundary receipt valid left right).mp edge) cause identity path
      · intro path
        exact Relation.ReflTransGen.mono (fun left right edge =>
          (catalogue_uses_iff boundary receipt valid left right).mpr edge) cause identity path
    rw [same, Relation.reflTransGen_iff_eq_or_transGen]
    simp only [eq_comm]
  · contradiction

namespace AncestryControls

def diamond : CausalReceipt Nat :=
  ⟨[4], [⟨1, []⟩, ⟨2, [1]⟩, ⟨3, [1]⟩, ⟨4, [2, 3]⟩]⟩

theorem shared_producer_is_retained_once :
    diamond.ancestors? [] 4 = some [4, 2, 3, 1] := by decide

theorem distinct_equal_uses_keep_distinct_queries :
    Controls.shared.ancestors? [] 2 = some [2, 1] ∧
      Controls.shared.ancestors? [] 3 = some [3, 1] := by decide

theorem missing_is_not_recorded_parentless :
    Controls.shared.ancestors? [] 0 = none ∧
      Controls.shared.ancestors? [] 1 = some [1] := by decide

theorem removed_sharing_changes_ancestry :
    Controls.shared.ancestors? [] 3 ≠ Controls.erasedSharing.ancestors? [] 3 := by decide

theorem captured_boundary_stays_visible :
    (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat).ancestors? [9] 1 = some [1, 9] := by decide

theorem missing_edge_target_refuses :
    (⟨[1], [⟨1, [9]⟩]⟩ : CausalReceipt Nat).ancestors? [] 1 = none := by decide

theorem duplicate_identity_refuses :
    (⟨[1], [⟨1, []⟩, ⟨1, []⟩]⟩ : CausalReceipt Nat).ancestors? [] 1 = none := by decide

theorem cycle_refuses :
    (⟨[2], [⟨1, [2]⟩, ⟨2, [1]⟩]⟩ : CausalReceipt Nat).ancestors? [] 2 = none := by decide

end AncestryControls

private def independentReceipt : CausalReceipt Nat where
  roots := [2]
  events :=
    [ { event := 1, directCauses := [] }
    , { event := 2, directCauses := [] } ]

private def dependentReceipt : CausalReceipt Nat where
  roots := [2]
  events :=
    [ { event := 1, directCauses := [] }
    , { event := 2, directCauses := [1] } ]

/-- Positive discriminator: flattening retains both event occurrences in
their exported order. -/
example : dependentReceipt.flattenedSupport = [1, 2] := rfl

/-- Negative discriminator: an independent pair and a causal chain have the
same flattened support. -/
example : independentReceipt.flattenedSupport =
    dependentReceipt.flattenedSupport := rfl

theorem independentReceipt_ne_dependentReceipt :
    independentReceipt ≠ dependentReceipt := by
  intro equal
  have eventsEqual := congrArg CausalReceipt.events equal
  simp [independentReceipt, dependentReceipt] at eventsEqual

/-- Consequently, no decoder from flattened event support can recover the
causal receipt for every input. -/
theorem flattenedSupport_not_injective :
    ¬ Function.Injective
      (flattenedSupport : CausalReceipt Nat → List Nat) := by
  intro injective
  exact independentReceipt_ne_dependentReceipt
    (injective (by rfl))

section DependencyFinish


universe uEvent
variable {Event : Type uEvent}

/-- All required predecessor finishes, including repeated predecessor slots. -/
def predecessorPeak (times : Event → Nat) (causes : List Event) : Nat :=
  (causes.map times).foldr max 0

theorem predecessorPeak_mono (earlier later : Event → Nat) (causes : List Event)
    (bounded : ∀ cause ∈ causes, earlier cause ≤ later cause) :
    predecessorPeak earlier causes ≤ predecessorPeak later causes := by
  induction causes with
  | nil => rfl
  | cons cause rest ih =>
      exact max_le_max (bounded cause List.mem_cons_self)
        (ih (fun other present => bounded other (List.mem_cons_of_mem _ present)))

theorem predecessorPeak_congr (first second : Event → Nat) (causes : List Event)
    (same : ∀ cause ∈ causes, first cause = second cause) :
    predecessorPeak first causes = predecessorPeak second causes := by
  induction causes with
  | nil => rfl
  | cons cause rest ih =>
      change max (first cause) (predecessorPeak first rest) =
        max (second cause) (predecessorPeak second rest)
      rw [same cause List.mem_cons_self,
        ih (fun other present => same other (List.mem_cons_of_mem _ present))]

variable [DecidableEq Event]

/-- Install one event's weighted earliest finish; its prerequisites are read
from the already installed finishes. -/
def advanceFinish (duration : Event → Nat) (times : Event → Nat)
    (event : CausalEvent Event) : Event → Nat :=
  Function.update times event.event
    (predecessorPeak times event.directCauses + duration event.event)

/-- Dynamic programming over the existing ordered occurrence graph. Boundary
finishes are supplied by the captured earlier execution, not reconstructed. -/
def finishTimes (duration : Event → Nat) (initial : Event → Nat) :
    List (CausalEvent Event) → (Event → Nat)
  | [] => initial
  | event :: rest => finishTimes duration (advanceFinish duration initial event) rest

/-- Fresh chronological insertion never rewrites a finish already available
at the captured boundary. -/
theorem finishTimes_preserves_available (duration : Event → Nat)
    (initial : Event → Nat) (available : List Event) (events : List (CausalEvent Event))
    (ordered : Ordered available events) (identity : Event) (present : identity ∈ available) :
    finishTimes duration initial events identity = initial identity := by
  induction events generalizing initial available with
  | nil => rfl
  | cons event rest ih =>
      rcases ordered with ⟨fresh, _, tail⟩
      rw [finishTimes, ih _ (available ++ [event.event]) tail
        (List.mem_append_left _ present)]
      have different : identity ≠ event.event := by
        rintro rfl
        exact fresh present
      simp [advanceFinish, different]

/-- Every installed event satisfies its dependency equation in the completed
map. Later independent occurrences cannot change its predecessor finishes. -/
theorem finishTimes_equations (duration : Event → Nat) (initial : Event → Nat)
    (available : List Event) (events : List (CausalEvent Event))
    (ordered : Ordered available events) :
    ∀ event ∈ events, finishTimes duration initial events event.event =
      predecessorPeak (finishTimes duration initial events) event.directCauses +
        duration event.event := by
  induction events generalizing initial available with
  | nil => intro event present; cases present
  | cons head rest ih =>
      rcases ordered with ⟨fresh, causes, tail⟩
      intro event present
      rcases List.mem_cons.mp present with same | member
      · subst event
        have own := finishTimes_preserves_available duration
          (advanceFinish duration initial head) (available ++ [head.event]) rest tail
          head.event (by simp)
        have prior := predecessorPeak_congr
          (finishTimes duration (advanceFinish duration initial head) rest)
          (advanceFinish duration initial head) head.directCauses (by
            intro cause member
            exact finishTimes_preserves_available duration _ _ rest tail cause
              (List.mem_append_left _ (causes cause member)))
        simp only [finishTimes]
        rw [own, prior]
        have earlier := predecessorPeak_congr (advanceFinish duration initial head)
          initial head.directCauses (by
            intro cause present
            have different : cause ≠ head.event := by
              rintro rfl
              exact fresh (causes head.event present)
            simp [advanceFinish, different])
        rw [earlier]
        simp only [advanceFinish, Function.update_self]
      · exact ih (advanceFinish duration initial head) (available ++ [head.event])
          tail event member

/-- A feasible finish assignment respects every retained immediate edge. -/
def FeasibleFinishes (duration times : Event → Nat) (events : List (CausalEvent Event)) : Prop :=
  ∀ event ∈ events,
    predecessorPeak times event.directCauses + duration event.event ≤ times event.event

/-- The independently specified feasible assignment bounds every step of the
earliest-finish computation. No chronological-order assumption supplies this
comparison; feasibility is checked against the actual graph. -/
theorem finishTimes_le_feasible (duration initial candidate : Event → Nat)
    (events : List (CausalEvent Event)) (boundaryBound : ∀ event, initial event ≤ candidate event)
    (feasible : FeasibleFinishes duration candidate events) :
    ∀ event, finishTimes duration initial events event ≤ candidate event := by
  induction events generalizing initial with
  | nil => exact boundaryBound
  | cons head rest ih =>
      apply ih (advanceFinish duration initial head)
      · intro event
        by_cases same : event = head.event
        · subst event
          simp only [advanceFinish, Function.update_self]
          exact (Nat.add_le_add_right
            (predecessorPeak_mono initial candidate head.directCauses
              (fun cause _ => boundaryBound cause)) _).trans
                (feasible head List.mem_cons_self)
        · simpa [advanceFinish, same] using boundaryBound event
      · intro event present
        exact feasible event (List.mem_cons_of_mem _ present)

/-- The computed map is feasible for the declared ordered dependency graph. -/
theorem finishTimes_feasible (duration initial : Event → Nat) (available : List Event)
    (events : List (CausalEvent Event)) (ordered : Ordered available events) :
    FeasibleFinishes duration (finishTimes duration initial events) events := by
  intro event present
  exact le_of_eq (finishTimes_equations duration initial available events ordered event present).symm

/-- Occurrence work is summed once; dependency span reads the weighted
earliest finishes. Graph validation and native edge authentication are distinct. -/
def dependencyReadout (receipt : CausalReceipt Event)
    (cost : Event → Mettapedia.Algebra.WorkSpan) : Mettapedia.Algebra.WorkSpan :=
  ⟨(receipt.flattenedSupport.map (fun event => (cost event).work)).sum,
    predecessorPeak (finishTimes (fun event => (cost event).span) (fun _ => 0) receipt.events)
      receipt.flattenedSupport⟩

/-- With no captured boundary, the dependency span is no larger than any
feasible finish assignment for this same occurrence graph. This excludes
scheduling overhead and does not choose a processor allocation. -/
theorem dependencyReadout_span_le (receipt : CausalReceipt Event)
    (cost : Event → Mettapedia.Algebra.WorkSpan) (candidate : Event → Nat)
    (feasible : FeasibleFinishes (fun event => (cost event).span) candidate receipt.events) :
    (dependencyReadout receipt cost).span ≤ predecessorPeak candidate receipt.flattenedSupport :=
  predecessorPeak_mono _ _ _ (fun event _ =>
    finishTimes_le_feasible _ _ _ _ (fun _ => Nat.zero_le _) feasible event)

namespace DependencyControls

def migrating : CausalReceipt Nat :=
  ⟨[2], [⟨0, []⟩, ⟨1, []⟩, ⟨2, [0, 1]⟩]⟩

def missingOwner : CausalReceipt Nat :=
  ⟨[2], [⟨0, []⟩, ⟨1, []⟩, ⟨2, [1]⟩]⟩

def missingWorker : CausalReceipt Nat :=
  ⟨[2], [⟨0, []⟩, ⟨1, []⟩, ⟨2, [0]⟩]⟩

def ownerHeavy (event : Nat) : Mettapedia.Algebra.WorkSpan :=
  if event = 0 then ⟨5, 5⟩ else if event = 1 then ⟨1, 1⟩ else ⟨2, 2⟩

def workerHeavy (event : Nat) : Mettapedia.Algebra.WorkSpan :=
  if event = 0 then ⟨2, 2⟩ else if event = 1 then ⟨5, 5⟩ else ⟨2, 2⟩

theorem owner_migration_retains_precedence :
    check [] migrating = true ∧ dependencyReadout migrating ownerHeavy = ⟨8, 7⟩ ∧
      dependencyReadout missingOwner ownerHeavy = ⟨8, 5⟩ := by decide +kernel

theorem physical_worker_order_retains_precedence :
    check [] migrating = true ∧ dependencyReadout migrating workerHeavy = ⟨9, 7⟩ ∧
      dependencyReadout missingWorker workerHeavy = ⟨9, 5⟩ := by decide +kernel

theorem repeated_predecessor_slots_do_not_repeat_work :
    let receipt : CausalReceipt Nat := ⟨[1], [⟨0, []⟩, ⟨1, [0, 0]⟩]⟩
    check [] receipt = true ∧ dependencyReadout receipt ownerHeavy = ⟨6, 6⟩ := by decide +kernel

end DependencyControls


end DependencyFinish

section ScheduledDependencies

universe uEvent uOwner uWorker

/-- One supplied execution occurrence and its exclusive owner and worker.
The log's authenticity is a separate native observation obligation. -/
structure ScheduledOccurrence (Event : Type uEvent) (Owner : Type uOwner)
    (Worker : Type uWorker) where
  identity : Event
  owner : Owner
  worker : Worker
  deriving DecidableEq

variable {Event : Type uEvent} {Owner : Type uOwner} {Worker : Type uWorker}

/-- A reference scan finds the last occurrence of the selected role. -/
def lastScheduled? {Key : Type*} [DecidableEq Key]
    (key : ScheduledOccurrence Event Owner Worker → Key) (selected : Key)
    (previous : List (ScheduledOccurrence Event Owner Worker)) : Option Event :=
  (previous.reverse.find? (fun event => decide (key event = selected))).map
    ScheduledOccurrence.identity

theorem lastScheduled?_mem {Key : Type*} [DecidableEq Key]
    (key : ScheduledOccurrence Event Owner Worker → Key) (selected : Key)
    (previous : List (ScheduledOccurrence Event Owner Worker)) (identity : Event)
    (found : lastScheduled? key selected previous = some identity) :
    identity ∈ previous.map ScheduledOccurrence.identity := by
  obtain ⟨event, present, same⟩ := Option.map_eq_some_iff.mp found
  exact List.mem_map.mpr ⟨event, by
    simpa using List.mem_of_find?_eq_some present, same⟩

theorem lastScheduled?_append_same {Key : Type*} [DecidableEq Key]
    (key : ScheduledOccurrence Event Owner Worker → Key)
    (previous : List (ScheduledOccurrence Event Owner Worker))
    (event : ScheduledOccurrence Event Owner Worker) :
    lastScheduled? key (key event) (previous ++ [event]) = some event.identity := by
  simp [lastScheduled?, List.reverse_append]

theorem lastScheduled?_append_other {Key : Type*} [DecidableEq Key]
    (key : ScheduledOccurrence Event Owner Worker → Key) (selected : Key)
    (previous : List (ScheduledOccurrence Event Owner Worker))
    (event : ScheduledOccurrence Event Owner Worker) (different : key event ≠ selected) :
    lastScheduled? key selected (previous ++ [event]) = lastScheduled? key selected previous := by
  simp [lastScheduled?, List.reverse_append, different]

variable [DecidableEq Owner] [DecidableEq Worker]

/-- Both roles contribute their preceding occurrence; coincident edges remain
two slots, while occurrence work is still counted once. -/
def scheduledCauses (previous : List (ScheduledOccurrence Event Owner Worker))
    (event : ScheduledOccurrence Event Owner Worker) : List Event :=
  (lastScheduled? ScheduledOccurrence.owner event.owner previous).toList ++
    (lastScheduled? ScheduledOccurrence.worker event.worker previous).toList

theorem scheduledCauses_known (previous : List (ScheduledOccurrence Event Owner Worker))
    (event : ScheduledOccurrence Event Owner Worker) (cause : Event)
    (present : cause ∈ scheduledCauses previous event) :
    cause ∈ previous.map ScheduledOccurrence.identity := by
  rcases List.mem_append.mp present with owner | worker
  · exact lastScheduled?_mem ScheduledOccurrence.owner event.owner previous cause (by simpa using owner)
  · exact lastScheduled?_mem ScheduledOccurrence.worker event.worker previous cause (by simpa using worker)

def scheduledEvents (previous : List (ScheduledOccurrence Event Owner Worker)) :
    List (ScheduledOccurrence Event Owner Worker) → List (CausalEvent Event)
  | [] => []
  | event :: rest => ⟨event.identity, scheduledCauses previous event⟩ ::
      scheduledEvents (previous ++ [event]) rest

theorem scheduledEvents_support (previous pending : List (ScheduledOccurrence Event Owner Worker)) :
    (scheduledEvents previous pending).map CausalEvent.event = pending.map ScheduledOccurrence.identity := by
  induction pending generalizing previous with
  | nil => rfl
  | cons event rest ih => simp [scheduledEvents, ih]


/-- Splitting recording into cohorts preserves the same role dependencies
when the later cohort receives the complete preceding execution log. -/
theorem scheduledEvents_append
    (previous first second : List (ScheduledOccurrence Event Owner Worker)) :
    scheduledEvents previous (first ++ second) =
      scheduledEvents previous first ++ scheduledEvents (previous ++ first) second := by
  induction first generalizing previous with
  | nil => simp [scheduledEvents]
  | cons event rest ih => simp [scheduledEvents, ih, List.append_assoc]

theorem scheduledEvents_ordered (previous pending : List (ScheduledOccurrence Event Owner Worker))
    (distinct : (previous.map ScheduledOccurrence.identity ++
      pending.map ScheduledOccurrence.identity).Nodup) :
    Ordered (previous.map ScheduledOccurrence.identity) (scheduledEvents previous pending) := by
  induction pending generalizing previous with
  | nil => trivial
  | cons event rest ih =>
      have disjoint := List.disjoint_of_nodup_append distinct
      have fresh : event.identity ∉ previous.map ScheduledOccurrence.identity := by
        intro present
        exact (List.disjoint_left.mp disjoint present) (by simp)
      have nextDistinct : ((previous ++ [event]).map ScheduledOccurrence.identity ++
          rest.map ScheduledOccurrence.identity).Nodup := by
        simpa only [List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.singleton_append] using distinct
      refine ⟨fresh, scheduledCauses_known previous event, ?_⟩
      simpa only [List.map_append, List.map_cons, List.map_nil] using ih _ nextDistinct

def scheduledReceipt (events : List (ScheduledOccurrence Event Owner Worker)) : CausalReceipt Event :=
  ⟨events.map ScheduledOccurrence.identity, scheduledEvents [] events⟩

theorem scheduledReceipt_wellFormed (events : List (ScheduledOccurrence Event Owner Worker))
    (distinct : (events.map ScheduledOccurrence.identity).Nodup) :
    (scheduledReceipt events).WellFormed [] := by
  refine ⟨by simp, scheduledEvents_ordered [] events (by simpa using distinct), ?_⟩
  intro root present
  simpa only [known, flattenedSupport, scheduledReceipt, List.nil_append,
    scheduledEvents_support] using present

namespace ScheduledControls

def occurrences : List (ScheduledOccurrence Nat Nat Nat) :=
  [⟨1, 11, 0⟩, ⟨3, 22, 1⟩, ⟨2, 11, 1⟩, ⟨4, 22, 0⟩]

def units (identity : Nat) : Mettapedia.Algebra.WorkSpan :=
  let amount := if identity = 1 then 1 else if identity = 2 then 3 else if identity = 3 then 5 else 7
  ⟨amount, amount⟩

theorem exact_owner_worker_graph :
    scheduledReceipt occurrences =
      ⟨[1,3,2,4], [⟨1,[]⟩, ⟨3,[]⟩, ⟨2,[1,3]⟩, ⟨4,[3,1]⟩]⟩ ∧
    check [] (scheduledReceipt occurrences) = true ∧
    dependencyReadout (scheduledReceipt occurrences) units = ⟨16,12⟩ := by
  decide +kernel

theorem duplicate_identity_refused :
    check [] (scheduledReceipt ([⟨1,11,0⟩,⟨1,22,1⟩] :
      List (ScheduledOccurrence Nat Nat Nat))) = false := by decide +kernel

theorem coincident_roles_preserve_both_slots :
    scheduledReceipt ([⟨1,11,0⟩,⟨2,11,0⟩] : List (ScheduledOccurrence Nat Nat Nat)) =
      ⟨[1,2], [⟨1,[]⟩,⟨2,[1,1]⟩]⟩ := by decide +kernel


/-- A graph with forgotten preceding roles can pass the structural checker
and still understate the execution dependency span. -/
theorem reset_between_cohorts_loses_dependency_span :
    let reset : CausalReceipt Nat := ⟨[1,3,2,4],
      scheduledEvents [] (occurrences.take 2) ++ scheduledEvents [] (occurrences.drop 2)⟩
    check [] reset = true ∧ dependencyReadout reset units = ⟨16,7⟩ ∧
      dependencyReadout (scheduledReceipt occurrences) units = ⟨16,12⟩ := by
  decide +kernel

end ScheduledControls
end ScheduledDependencies

/-- One occurrence and its predecessor set. This chosen readout forgets
predecessor-slot order and repetition while retaining the occurrence itself. -/
def dependencyNode [DecidableEq Event] (event : CausalEvent Event) : Event × Finset Event :=
  (event.event, event.directCauses.toFinset)

/-- A causal graph observation forgets chronology, retaining every vertex
occurrence and every root occurrence, together with their dependency sets. -/
def dependencyView [DecidableEq Event] (receipt : CausalReceipt Event) :
    Multiset Event × Multiset (Event × Finset Event) :=
  (receipt.roots, receipt.events.map dependencyNode)

theorem dependencyView_of_perm [DecidableEq Event] (left right : CausalReceipt Event)
    (roots : left.roots.Perm right.roots)
    (nodes : (left.events.map dependencyNode).Perm (right.events.map dependencyNode)) :
    left.dependencyView = right.dependencyView := by
  exact Prod.ext (Multiset.coe_eq_coe.mpr roots) (Multiset.coe_eq_coe.mpr nodes)

/-- Matching graph observations retain a node with its actual identity and
predecessor set, independently of chronology or repeated predecessor slots. -/
theorem dependencyView_node [DecidableEq Event] (left right : CausalReceipt Event)
    (same : left.dependencyView = right.dependencyView)
    (node : CausalEvent Event) (member : node ∈ left.events) :
    ∃ other ∈ right.events, other.event = node.event ∧
      other.directCauses.toFinset = node.directCauses.toFinset := by
  have rows := congrArg Prod.snd same
  change (left.events.map dependencyNode : Multiset (Event × Finset Event)) =
    (right.events.map dependencyNode : Multiset (Event × Finset Event)) at rows
  have present : dependencyNode node ∈ (left.events.map dependencyNode : Multiset (Event × Finset Event)) :=
    List.mem_map.mpr ⟨node, member, rfl⟩
  rw [rows] at present
  obtain ⟨other, otherMember, sameNode⟩ := List.mem_map.mp present
  exact ⟨other, otherMember, congrArg Prod.fst sameNode, congrArg Prod.snd sameNode⟩

/-- Equality of this causal readout retains every actual dependency. Equal
vertex support without the predecessor relation is insufficient. -/
theorem dependencyView_direct [DecidableEq Event] (left right : CausalReceipt Event)
    (same : left.dependencyView = right.dependencyView) (cause effect : Event) :
    left.Direct cause effect ↔ right.Direct cause effect := by
  have forward : ∀ first second : CausalReceipt Event,
      first.dependencyView = second.dependencyView → first.Direct cause effect → second.Direct cause effect := by
    intro first second equal related
    rcases related with ⟨node, member, target, predecessor⟩
    obtain ⟨other, otherMember, sameTarget, sameParents⟩ := dependencyView_node first second equal node member
    refine ⟨other, otherMember, sameTarget.trans target, ?_⟩
    apply List.mem_toFinset.mp
    rw [sameParents]
    exact List.mem_toFinset.mpr predecessor
  exact ⟨forward left right same, forward right left same.symm⟩

/-- Vertex multiplicities survive the chosen graph observation. -/
theorem dependencyView_support_perm [DecidableEq Event] (left right : CausalReceipt Event)
    (same : left.dependencyView = right.dependencyView) :
    left.flattenedSupport.Perm right.flattenedSupport := by
  have rows := congrArg (fun view => view.2.map Prod.fst) same
  apply Multiset.coe_eq_coe.mp
  simpa [dependencyView, dependencyNode, flattenedSupport, List.map_map, Function.comp_def] using rows

/-- Maximum predecessor finish depends on membership, not slot repetition. -/
theorem predecessorPeak_le_iff (times : Event → Nat) (causes : List Event) (bound : Nat) :
    predecessorPeak times causes ≤ bound ↔ ∀ cause ∈ causes, times cause ≤ bound := by
  induction causes with
  | nil => simp [predecessorPeak]
  | cons cause rest ih =>
      change max (times cause) (predecessorPeak times rest) ≤ bound ↔ _
      simp only [max_le_iff, ih, List.forall_mem_cons]

theorem predecessorPeak_of_members (times : Event → Nat) (first second : List Event)
    (same : ∀ event, event ∈ first ↔ event ∈ second) :
    predecessorPeak times first = predecessorPeak times second := by
  apply Nat.le_antisymm
  · rw [predecessorPeak_le_iff]
    intro event present
    exact (predecessorPeak_le_iff times second _).mp le_rfl event ((same event).mp present)
  · rw [predecessorPeak_le_iff]
    intro event present
    exact (predecessorPeak_le_iff times first _).mp le_rfl event ((same event).mpr present)

/-- Feasibility is a property of the actual graph observation. -/
theorem feasibleFinishes_of_dependencyView [DecidableEq Event]
    (left right : CausalReceipt Event) (same : left.dependencyView = right.dependencyView)
    (duration times : Event → Nat) (feasible : FeasibleFinishes duration times right.events) :
    FeasibleFinishes duration times left.events := by
  intro node member
  obtain ⟨other, otherMember, sameEvent, sameParents⟩ := dependencyView_node left right same node member
  have samePeak : predecessorPeak times node.directCauses = predecessorPeak times other.directCauses := by
    apply predecessorPeak_of_members
    intro event
    exact List.mem_toFinset.symm.trans ((congrArg (event ∈ ·) sameParents).symm ▸ List.mem_toFinset)
  rw [samePeak, ← sameEvent]
  exact feasible other otherMember

/-- Earliest finishes agree on every identity for two valid topological
readings of the same occurrence graph. The least-feasible comparison supplies
both inequalities; equal event bags alone do not suffice. -/
theorem finishTimes_of_dependencyView [DecidableEq Event]
    (left right : CausalReceipt Event) (same : left.dependencyView = right.dependencyView)
    (leftOrdered : Ordered [] left.events) (rightOrdered : Ordered [] right.events)
    (duration : Event → Nat) :
    finishTimes duration (fun _ => 0) left.events =
      finishTimes duration (fun _ => 0) right.events := by
  funext event
  apply Nat.le_antisymm
  · apply finishTimes_le_feasible duration (fun _ => 0)
      (finishTimes duration (fun _ => 0) right.events) left.events
      (fun _ => Nat.zero_le _)
    exact feasibleFinishes_of_dependencyView left right same duration _
      (finishTimes_feasible duration (fun _ => 0) [] right.events rightOrdered)
  · apply finishTimes_le_feasible duration (fun _ => 0)
      (finishTimes duration (fun _ => 0) left.events) right.events
      (fun _ => Nat.zero_le _)
    exact feasibleFinishes_of_dependencyView right left same.symm duration _
      (finishTimes_feasible duration (fun _ => 0) [] left.events leftOrdered)

/-- Source work and dependency span factor through the selected causal view.
This is not a statement about elapsed time, scheduling overhead or permission. -/
theorem dependencyReadout_of_dependencyView [DecidableEq Event]
    (left right : CausalReceipt Event) (same : left.dependencyView = right.dependencyView)
    (leftOrdered : Ordered [] left.events) (rightOrdered : Ordered [] right.events)
    (cost : Event → Mettapedia.Algebra.WorkSpan) :
    left.dependencyReadout cost = right.dependencyReadout cost := by
  have support := dependencyView_support_perm left right same
  have times := finishTimes_of_dependencyView left right same leftOrdered rightOrdered
    (fun event => (cost event).span)
  apply Mettapedia.Algebra.WorkSpan.ext
  · exact (support.map (fun event => (cost event).work)).sum_eq
  · change predecessorPeak _ left.flattenedSupport = predecessorPeak _ right.flattenedSupport
    rw [times]
    exact predecessorPeak_of_members _ _ _ (fun event => support.mem_iff)

namespace DependencyViewControls

/-- Equal occurrence counts distinguish a parallel pair from a causal chain. -/
theorem counts_do_not_determine_span :
    check [] independentReceipt = true ∧ check [] dependentReceipt = true ∧
    dependencyReadout independentReceipt (fun _ => ⟨1, 1⟩) = ⟨2, 1⟩ ∧
    dependencyReadout dependentReceipt (fun _ => ⟨1, 1⟩) = ⟨2, 2⟩ := by decide

/-- Reordering independent vertices and repeating predecessor slots preserve
this observer, while both physical producer occurrences still contribute. -/
theorem reordered_slots_keep_source_cost :
    let first : CausalReceipt Nat := ⟨[3], [⟨1, []⟩, ⟨2, []⟩, ⟨3, [1, 2]⟩]⟩
    let second : CausalReceipt Nat := ⟨[3], [⟨2, []⟩, ⟨1, []⟩, ⟨3, [2, 1, 2]⟩]⟩
    first.dependencyView = second.dependencyView ∧
      check [] first = true ∧ check [] second = true ∧
      dependencyReadout first (fun _ => ⟨1, 1⟩) = ⟨3, 2⟩ ∧
      dependencyReadout second (fun _ => ⟨1, 1⟩) = ⟨3, 2⟩ := by decide

end DependencyViewControls

/-! ## Resource frontiers

A requested history reader derives producer and read-before-consume edges
from the supplied finite resource incidences. This builder uses the existing
causal receipt. It neither checks resource availability nor grants execution.
The resource-word checker supplies that separate operational judgment.
-/

namespace ResourceFrontier

variable {Resource Identity Action : Type*}

/-- The last producer of a physical resource and its outstanding readers.
Consumed resources drop both entries; newly produced resources get their
actual producing occurrence. -/
structure State (Resource Identity : Type*) where
  producer : Resource → Option Identity
  readers : Resource → List Identity

/-- Initial resources have no producer in the requested recording interval. -/
def empty : State Resource Identity := ⟨fun _ => none, fun _ => []⟩

/-- All producer dependencies and all reads that a consume must follow.
Predecessor slots remain explicit; consumers may separately forget repeats. -/
def parents (state : State Resource Identity) (consumed read : List Resource) : List Identity :=
  (consumed ++ read).filterMap state.producer ++ consumed.flatMap state.readers

/-- Update the two frontiers once, using the same physical resource keys as
the selected operation. This carries no execution or scheduling decision. -/
def advance [DecidableEq Resource] (state : State Resource Identity) (identity : Identity)
    (consumed read produced : List Resource) : State Resource Identity where
  producer := fun resource =>
    if resource ∈ produced then some identity
    else if resource ∈ consumed then none else state.producer resource
  readers := fun resource =>
    let previous := if resource ∈ consumed then [] else state.readers resource
    if resource ∈ read then identity :: previous else previous

/-- Every retained frontier reference names a captured or earlier occurrence. -/
def References (state : State Resource Identity) (available : List Identity) : Prop :=
  (∀ resource identity, state.producer resource = some identity → identity ∈ available) ∧
  (∀ resource identity, identity ∈ state.readers resource → identity ∈ available)

theorem empty_references (available : List Identity) :
    References (empty : State Resource Identity) available := by
  constructor
  · intro resource identity present
    cases present
  · intro resource identity present
    cases present

theorem mem_parents (state : State Resource Identity) (consumed read : List Resource)
    (identity : Identity) :
    identity ∈ parents state consumed read ↔
      (∃ resource ∈ consumed ++ read, state.producer resource = some identity) ∨
      (∃ resource ∈ consumed, identity ∈ state.readers resource) := by
  simp only [parents, List.mem_append, List.mem_filterMap, List.mem_flatMap]

theorem parents_referenced (state : State Resource Identity) (available : List Identity)
    (valid : References state available) (consumed read : List Resource) :
    ∀ identity ∈ parents state consumed read, identity ∈ available := by
  intro identity present
  rcases (mem_parents state consumed read identity).mp present with
    ⟨resource, _, producer⟩ | ⟨resource, _, reader⟩
  · exact valid.1 resource identity producer
  · exact valid.2 resource identity reader

theorem advance_references [DecidableEq Resource] (state : State Resource Identity)
    (available : List Identity) (valid : References state available) (identity : Identity)
    (consumed read produced : List Resource) :
    References (advance state identity consumed read produced) (available ++ [identity]) := by
  constructor
  · intro resource candidate present
    dsimp only [advance] at present
    split at present
    · cases present
      exact List.mem_append_right _ List.mem_cons_self
    · split at present
      · cases present
      · exact List.mem_append_left _ (valid.1 resource candidate present)
  · intro resource candidate present
    dsimp only [advance] at present
    split at present
    · rcases List.mem_cons.mp present with same | prior
      · rw [same]
        exact List.mem_append_right _ List.mem_cons_self
      · split at prior
        · cases prior
        · exact List.mem_append_left _ (valid.2 resource candidate prior)
    · split at present
      · cases present
      · exact List.mem_append_left _ (valid.2 resource candidate present)

/-- A finite word is read once. Its event identities come from the source
occurrences, independently of equal payloads or equal footprints. -/
def run [DecidableEq Resource] (identity : Action → Identity)
    (consume read produce : Action → List Resource) :
    List Action → State Resource Identity → List (CausalEvent Identity) × State Resource Identity
  | [], state => ([], state)
  | action :: rest, state =>
      let node := CausalEvent.mk (identity action) (parents state (consume action) (read action))
      let next := advance state (identity action) (consume action) (read action) (produce action)
      let suffix := run identity consume read produce rest next
      (node :: suffix.1, suffix.2)

theorem run_identities [DecidableEq Resource] (identity : Action → Identity)
    (consume read produce : Action → List Resource) (word : List Action)
    (state : State Resource Identity) :
    ((run identity consume read produce word state).1).map CausalEvent.event = word.map identity := by
  induction word generalizing state with
  | nil => rfl
  | cons action rest ih =>
      change identity action :: _ = identity action :: _
      exact congrArg (identity action :: ·) (ih _)

/-- A suspended reader resumes with its actual producer and reader frontiers,
so split reading equals reading the concatenated word. -/
theorem run_append [DecidableEq Resource] (identity : Action → Identity)
    (consume read produce : Action → List Resource) (first second : List Action)
    (state : State Resource Identity) :
    run identity consume read produce (first ++ second) state =
      let left := run identity consume read produce first state
      let right := run identity consume read produce second left.2
      (left.1 ++ right.1, right.2) := by
  induction first generalizing state with
  | nil => rfl
  | cons action rest ih =>
      simp only [List.cons_append, run, ih, List.cons_append]

theorem run_ordered [DecidableEq Resource] (identity : Action → Identity)
    (consume read produce : Action → List Resource) (word : List Action)
    (state : State Resource Identity) (available : List Identity)
    (valid : References state available) (fresh : (available ++ word.map identity).Nodup) :
    CausalReceipt.Ordered available (run identity consume read produce word state).1 := by
  induction word generalizing state available with
  | nil => trivial
  | cons action rest ih =>
      have distinct : (available ++ identity action :: rest.map identity).Nodup := fresh
      have absent : identity action ∉ available := by
        have disjoint := List.disjoint_of_nodup_append distinct
        exact fun member => (List.disjoint_left.mp disjoint) member List.mem_cons_self
      refine ⟨absent, parents_referenced state available valid _ _, ?_⟩
      apply ih _ (available ++ [identity action])
        (advance_references state available valid _ _ _ _)
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using fresh

/-- The full requested history retains every occurrence as a selected root. -/
def receipt [DecidableEq Resource] (identity : Action → Identity)
    (consume read produce : Action → List Resource) (word : List Action) : CausalReceipt Identity :=
  let events := (run identity consume read produce word empty).1
  ⟨events.map CausalEvent.event, events⟩

theorem receipt_wellFormed [DecidableEq Resource] (identity : Action → Identity)
    (consume read produce : Action → List Resource) (word : List Action)
    (fresh : (word.map identity).Nodup) :
    CausalReceipt.WellFormed [] (receipt identity consume read produce word) := by
  refine ⟨by simp, ?_, ?_⟩
  · exact run_ordered identity consume read produce word empty [] (empty_references []) fresh
  · intro root present
    exact present

/-- Repeated source identities refuse instead of being merged as equal events. -/
def receipt? [DecidableEq Resource] [DecidableEq Identity] (identity : Action → Identity)
    (consume read produce : Action → List Resource) (word : List Action) :
    Option (CausalReceipt Identity) :=
  if (word.map identity).Nodup then some (receipt identity consume read produce word) else none

theorem receipt?_sound [DecidableEq Resource] [DecidableEq Identity]
    (identity : Action → Identity) (consume read produce : Action → List Resource)
    (word : List Action) (result : CausalReceipt Identity)
    (accepted : receipt? identity consume read produce word = some result) :
    CausalReceipt.WellFormed [] result ∧ result.flattenedSupport = word.map identity := by
  unfold receipt? at accepted
  split at accepted
  · next fresh =>
      cases Option.some.inj accepted
      exact ⟨receipt_wellFormed identity consume read produce word fresh,
        run_identities identity consume read produce word empty⟩
  · cases accepted

/-- Frontiers may retain readers in different orders. Their producer
identities and reader occurrences still agree. -/
def Equivalent (left right : State Resource Identity) : Prop :=
  left.producer = right.producer ∧ ∀ resource, (left.readers resource).Perm (right.readers resource)

theorem advance_equivalent [DecidableEq Resource] {left right : State Resource Identity}
    (same : Equivalent left right) (identity : Identity) (consumed read produced : List Resource) :
    Equivalent (advance left identity consumed read produced)
      (advance right identity consumed read produced) := by
  constructor
  · funext resource
    simp only [advance, same.1]
  · intro resource
    by_cases taken : resource ∈ consumed <;> by_cases inspected : resource ∈ read
    · simp [advance, taken, inspected]
    · simp [advance, taken, inspected]
    · simpa only [advance, if_neg taken, if_pos inspected] using
        (same.2 resource).cons identity
    · simpa only [advance, if_neg taken, if_neg inspected] using same.2 resource

theorem parents_equivalent {left right : State Resource Identity}
    (same : Equivalent left right) (consumed read : List Resource) :
    (parents left consumed read).Perm (parents right consumed read) := by
  unfold parents
  rw [same.1]
  exact (List.Perm.refl _).append (List.Perm.flatMap_left consumed (fun resource _ => same.2 resource))

theorem run_equivalent [DecidableEq Resource] [DecidableEq Identity]
    (identity : Action → Identity) (consume read produce : Action → List Resource)
    (word : List Action) {left right : State Resource Identity} (same : Equivalent left right) :
    ((run identity consume read produce word left).1.map dependencyNode =
      (run identity consume read produce word right).1.map dependencyNode) ∧
      Equivalent (run identity consume read produce word left).2
        (run identity consume read produce word right).2 := by
  induction word generalizing left right with
  | nil => exact ⟨rfl, same⟩
  | cons action rest ih =>
      have next := advance_equivalent same (identity action) (consume action) (read action) (produce action)
      obtain ⟨tail, final⟩ := ih next
      refine ⟨?_, final⟩
      change (identity action, (parents left (consume action) (read action)).toFinset) :: _ =
        (identity action, (parents right (consume action) (read action)).toFinset) :: _
      rw [List.toFinset_eq_of_perm _ _ (parents_equivalent same (consume action) (read action)), tail]

/-- Every written resource of either operation is absent from all accesses
of the other. Persistent reads may overlap. -/
def Independent (leftConsume leftRead leftProduce rightConsume rightRead rightProduce : List Resource) : Prop :=
  List.Disjoint (leftConsume ++ leftProduce) (rightConsume ++ rightRead ++ rightProduce) ∧
  List.Disjoint (rightConsume ++ rightProduce) (leftConsume ++ leftRead ++ leftProduce)

theorem Independent.symm {lc lr lp rc rr rp : List Resource} (separate : Independent lc lr lp rc rr rp) :
    Independent rc rr rp lc lr lp := ⟨separate.2, separate.1⟩

private theorem independent_left {lc lr lp rc rr rp : List Resource}
    (separate : Independent lc lr lp rc rr rp) (resource : Resource)
    (written : resource ∈ lc ∨ resource ∈ lp) :
    resource ∉ rc ∧ resource ∉ rr ∧ resource ∉ rp := by
  have left : resource ∈ lc ++ lp := List.mem_append.mpr written
  have away := (List.disjoint_left.mp separate.1) left
  simpa only [List.mem_append, not_or, and_assoc] using away

/-- Independent updates commute on producer identities and reader occurrences.
Reader ordering remains available in each original ordered history. -/
theorem advance_commutes [DecidableEq Resource] (state : State Resource Identity)
    (left right : Identity) (lc lr lp rc rr rp : List Resource)
    (separate : Independent lc lr lp rc rr rp) :
    Equivalent (advance (advance state left lc lr lp) right rc rr rp)
      (advance (advance state right rc rr rp) left lc lr lp) := by
  constructor
  · funext resource
    have awayL := independent_left separate resource
    have awayR := independent_left separate.symm resource
    by_cases pl : resource ∈ lp <;> by_cases pr : resource ∈ rp <;>
      by_cases cl : resource ∈ lc <;> by_cases cr : resource ∈ rc <;>
      simp_all [advance]
  · intro resource
    by_cases cl : resource ∈ lc
    · have away := independent_left separate resource (Or.inl cl)
      simp only [advance, if_pos cl, if_neg away.1, if_neg away.2.1]
      exact List.Perm.refl _
    · by_cases cr : resource ∈ rc
      · have away := independent_left separate.symm resource (Or.inl cr)
        simp only [advance, if_neg cl, if_pos cr, if_neg away.2.1]
        exact List.Perm.refl _
      · by_cases rl : resource ∈ lr
        · by_cases rr' : resource ∈ rr
          · simpa only [advance, if_neg cl, if_neg cr, if_pos rl, if_pos rr'] using
              List.Perm.swap left right (state.readers resource)
          · simp only [advance, if_neg cl, if_neg cr, if_pos rl, if_neg rr']
            exact List.Perm.refl _
        · by_cases rr' : resource ∈ rr
          · simp only [advance, if_neg cl, if_neg cr, if_neg rl, if_pos rr']
            exact List.Perm.refl _
          · simp only [advance, if_neg cl, if_neg cr, if_neg rl, if_neg rr']
            exact List.Perm.refl _

/-- Advancing an independent operation cannot change a selected operation's
producer or read-before-consume dependencies. -/
theorem parents_after_independent [DecidableEq Resource] (state : State Resource Identity)
    (right : Identity) (lc lr lp rc rr rp : List Resource)
    (separate : Independent lc lr lp rc rr rp) :
    parents (advance state right rc rr rp) lc lr = parents state lc lr := by
  apply congrArg₂ (· ++ ·)
  · apply List.filterMap_congr
    intro resource present
    have noProduce : resource ∉ rp := by
      intro written
      have away := independent_left separate.symm resource (Or.inr written)
      rcases List.mem_append.mp present with taken | read
      · exact away.1 taken
      · exact away.2.1 read
    have noConsume : resource ∉ rc := by
      intro written
      have away := independent_left separate.symm resource (Or.inl written)
      rcases List.mem_append.mp present with taken | read
      · exact away.1 taken
      · exact away.2.1 read
    simp only [advance, if_neg noProduce, if_neg noConsume]
  · apply List.flatMap_congr
    intro resource present
    have away := independent_left separate resource (Or.inl present)
    simp only [advance, if_neg away.1, if_neg away.2.1]

/-- Independent operations keep the same two dependency vertices and the
same remaining reader state. Only the original chronology is exchanged. -/
theorem run_swap [DecidableEq Resource] [DecidableEq Identity]
    (identity : Action → Identity) (consume read produce : Action → List Resource)
    (left right : Action) (suffix : List Action) (state : State Resource Identity)
    (separate : Independent (consume left) (read left) (produce left)
      (consume right) (read right) (produce right)) :
    ((run identity consume read produce (left :: right :: suffix) state).1.map dependencyNode).Perm
      ((run identity consume read produce (right :: left :: suffix) state).1.map dependencyNode) ∧
      Equivalent (run identity consume read produce (left :: right :: suffix) state).2
        (run identity consume read produce (right :: left :: suffix) state).2 := by
  have swapped := advance_commutes state (identity left) (identity right)
    (consume left) (read left) (produce left) (consume right) (read right) (produce right) separate
  obtain ⟨rest, final⟩ := run_equivalent identity consume read produce suffix swapped
  constructor
  · simp only [run, List.map_cons]
    rw [parents_after_independent state (identity left) _ _ _ _ _ _ separate.symm,
      parents_after_independent state (identity right) _ _ _ _ _ _ separate, rest]
    exact List.Perm.swap _ _ _
  · exact final

/-- A causal observation of the whole requested word is invariant under an
independent tile inside arbitrary prefixes and suffixes. Ordered words are
still available separately, and the observer retains all vertex identities. -/
theorem receipt_view_swap [DecidableEq Resource] [DecidableEq Identity]
    (identity : Action → Identity) (consume read produce : Action → List Resource)
    (earlier suffix : List Action) (left right : Action)
    (separate : Independent (consume left) (read left) (produce left)
      (consume right) (read right) (produce right)) :
    (receipt identity consume read produce (earlier ++ left :: right :: suffix)).dependencyView =
      (receipt identity consume read produce (earlier ++ right :: left :: suffix)).dependencyView := by
  apply dependencyView_of_perm
  · simp only [receipt, run_identities, List.map_append, List.map_cons]
    exact (List.Perm.refl _).append (List.Perm.swap _ _ _)
  · have swapped := (run_swap identity consume read produce left right suffix
        (run identity consume read produce earlier empty).2 separate).1
    simpa only [receipt, run_append, List.map_append] using
      (List.Perm.refl ((run identity consume read produce earlier empty).1.map dependencyNode)).append swapped

namespace Controls

private def consumes : Nat → List Nat
  | 1 => [4]
  | 10 => [1]
  | 20 => [2]
  | 30 => [3, 0]
  | _ => []

private def reads : Nat → List Nat
  | 10 | 20 => [0]
  | _ => []

private def produces : Nat → List Nat
  | 1 => [0, 1, 2, 3]
  | _ => []

/-- One production supports two separate read occurrences. -/
theorem shared_producer_two_reads :
    (receipt id consumes reads produces [1, 10, 20]).dependencyView =
      (receipt id consumes reads produces [1, 20, 10]).dependencyView ∧
      (receipt id consumes reads produces [1, 10, 20]).Direct 1 10 ∧
      (receipt id consumes reads produces [1, 10, 20]).Direct 1 20 := by
  unfold Direct
  decide

/-- A later consume retains both reads it must follow. Those are edges,
not just membership in the flattened event support. -/
theorem consume_keeps_both_readers :
    (receipt id consumes reads produces [1, 10, 20, 30]).Direct 10 30 ∧
      (receipt id consumes reads produces [1, 10, 20, 30]).Direct 20 30 ∧
      ¬ (receipt id consumes reads produces [1, 30, 10, 20]).Direct 10 30 := by
  unfold Direct
  decide

/-- Equal-looking uses cannot reuse one supplied occurrence identity. -/
theorem duplicate_occurrence_refused :
    receipt? id consumes reads produces [1, 10, 10] = none := by decide

end Controls

end ResourceFrontier

end CausalReceipt

/-! ## Demand annotations -/

/-- Whether a cell observation was demanded while matching a left-hand side
or while evaluating the selected right-hand side. -/
inductive DemandRole where
  | lhs
  | rhs
deriving DecidableEq, Repr

/-- Candidate-local information required to replay why an event was demanded. -/
structure DemandAnnotation (Event ExpectedType : Type) where
  event : Event
  role : DemandRole
  expectedType : ExpectedType
deriving DecidableEq, Repr

namespace DemandAnnotation

variable {Event ExpectedType : Type}

/-- The event-only projection used when role and expected type are absent from
the wire observation. -/
def erase (annotation : DemandAnnotation Event ExpectedType) : Event :=
  annotation.event

private def lhsDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .lhs, expectedType := false }

private def rhsDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .rhs, expectedType := false }

private def otherTypeDemand : DemandAnnotation Nat Bool :=
  { event := 7, role := .lhs, expectedType := true }

/-- Positive discriminator: erasure retains the referenced event occurrence. -/
example : lhsDemand.erase = 7 := rfl

/-- The event-only projection cannot distinguish left- from right-hand-side
demand. -/
theorem erase_role_not_injective :
    ¬ Function.Injective
      (erase : DemandAnnotation Nat Bool → Nat) := by
  intro injective
  have equalAnnotations : lhsDemand = rhsDemand :=
    injective (by rfl)
  have equalRoles := congrArg DemandAnnotation.role equalAnnotations
  cases equalRoles

/-- Nor can the same projection reconstruct the expected type. -/
theorem erase_expectedType_not_injective :
    ¬ Function.Injective
      (erase : DemandAnnotation Nat Bool → Nat) := by
  intro injective
  have equalAnnotations : lhsDemand = otherTypeDemand :=
    injective (by rfl)
  have equalTypes := congrArg DemandAnnotation.expectedType equalAnnotations
  simp [lhsDemand, otherTypeDemand] at equalTypes

end DemandAnnotation

/-! ## Interrupted frontiers -/

/-- A resource-interrupted execution together with the live frontier known to
the producer.  The existing external observation retains the answers and
reason but may omit `pending`. -/
structure InterruptedRunWitness (State Answer : Type) where
  answers : List (Answer × List Nat)
  reason : ResourceInterruption
  pending : List State
deriving DecidableEq, Repr

namespace InterruptedRunWitness

variable {State Answer : Type}

/-- Erase a producer-side interrupted frontier to the public run observation. -/
def erase (witness : InterruptedRunWitness State Answer) :
    RunObservation State Answer where
  answers := witness.answers
  stop := .interrupted witness.reason

private def waitingAtOne : InterruptedRunWitness Nat Nat where
  answers := [(7, [0])]
  reason := .fuelExhausted
  pending := [1]

private def waitingAtTwo : InterruptedRunWitness Nat Nat where
  answers := [(7, [0])]
  reason := .fuelExhausted
  pending := [2]

/-- Positive discriminator: answer occurrences and interruption reason remain
observable after the frontier is erased. -/
example : waitingAtOne.erase.answers = [(7, [0])] := rfl

example : waitingAtOne.erase.stop.externalInterruption =
    some .fuelExhausted := rfl

/-- Negative discriminator: two different live frontiers produce the same
external interruption observation. -/
example : waitingAtOne.erase = waitingAtTwo.erase := rfl

theorem waitingAtOne_ne_waitingAtTwo : waitingAtOne ≠ waitingAtTwo := by
  intro equal
  have pendingEqual := congrArg InterruptedRunWitness.pending equal
  simp [waitingAtOne, waitingAtTwo] at pendingEqual

/-- Therefore an answer-and-reason observation cannot reconstruct the live
frontier of every interrupted execution. -/
theorem erase_not_injective :
    ¬ Function.Injective
      (erase : InterruptedRunWitness Nat Nat → RunObservation Nat Nat) := by
  intro injective
  exact waitingAtOne_ne_waitingAtTwo (injective (by rfl))

end InterruptedRunWitness

end Mettapedia.Machines
