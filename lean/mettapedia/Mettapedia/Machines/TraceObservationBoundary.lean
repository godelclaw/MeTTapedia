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
