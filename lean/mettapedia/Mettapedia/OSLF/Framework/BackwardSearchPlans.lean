import Mettapedia.OSLF.Framework.BackwardSearch
import Mettapedia.GSLT.Core.BranchingTemporal

/-!
# Backward search plans

A presentation of backward search (`Presentation`) describes sets of states by nodes: finitely
many seed nodes cover the goal, and each node has finitely many predecessor nodes whose states
step into the node's set (`predecessors_sound`). At a good node they cover `◇` of its set, up to
the node's own states (`predecessors_complete`): backward narrowing of a linear pattern misses
exactly the steps inside its variables, and those start inside the pattern's set again. A node
may be a single state, or a pattern that stands for infinitely many states; the theorems do not
depend on which. Exact presentations, where every node is good and the predecessors describe
exactly `◇` (`ofExact`), also describe the initial chain level by level.

The presentation is a finitely branching system (`system`). A search plan is a scheduler for it
(`BranchingTemporal.Scheduler`): it chooses which live node to expand next. Then:

- every run is sound: every state an emitted node describes reaches the goal (`found_sound`);
- when every generated node is good, every fair plan is complete: every state that reaches the
  goal is eventually described (`fair_complete`), so all fair plans find the same states
  (`fair_plans_agree`), and breadth-first is exact (`breadthFirst_exact`);
- for exact presentations, the levels breadth-first expands in turn describe the initial chain of
  `goal ∨ ◇(-)` (`levels_denote_chain`);
- a run may stop with a certificate: when every emitted node is good and every live node is
  covered by emitted ones, the emitted nodes describe exactly the states that reach the goal,
  whatever the plan (`saturated_exact`). Then "cannot reach" is proved from finitely many nodes,
  also on infinite state spaces.

`answer` reads a run: `reaches`, `cannotReach` (only from a saturated run) or `unknown`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.BackwardSearch

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Core.BranchingTemporal

variable {X : Type*} {span : ReductionSpan X} {goal : X → Prop}

/-- **A presentation of backward search**: nodes describing sets of states, seeds covering the
goal, and finitely many predecessor nodes whose states step into the node's set; at a good node
they cover every such state outside the node's own set. -/
structure Presentation (span : ReductionSpan X) (goal : X → Prop) (Node : Type*) where
  denote : Node → X → Prop
  seeds : List Node
  predecessors : Node → List Node
  seeds_exact : ∀ state, goal state ↔ ∃ node ∈ seeds, denote node state
  /-- The nodes whose predecessors are complete. -/
  good : Node → Prop
  predecessors_sound : ∀ node, ∀ previous ∈ predecessors node, ∀ state,
    denote previous state → derivedDiamond span (denote node) state
  predecessors_complete : ∀ node, good node → ∀ state, derivedDiamond span (denote node) state →
    denote node state ∨ ∃ previous ∈ predecessors node, denote previous state

namespace Presentation

/-- **An exact presentation**: the predecessors describe exactly `◇` of every node's set. -/
def ofExact {Node : Type*} (denote : Node → X → Prop) (seeds : List Node) (predecessors : Node → List Node)
    (seeds_exact : ∀ state, goal state ↔ ∃ node ∈ seeds, denote node state)
    (exact : ∀ node state,
      (∃ previous ∈ predecessors node, denote previous state) ↔ derivedDiamond span (denote node) state) :
    Presentation span goal Node where
  denote := denote
  seeds := seeds
  predecessors := predecessors
  seeds_exact := seeds_exact
  good _ := True
  predecessors_sound node previous member state holds := (exact node state).mp ⟨previous, member, holds⟩
  predecessors_complete node _ state holds := Or.inr ((exact node state).mpr holds)

variable {Node : Type*} (presentation : Presentation span goal Node)

/-- The branching system of the search: every node is emitted, and expands to its predecessors. -/
def system : BranchingSystem Node Node := ⟨some, presentation.predecessors⟩

/-- The states described by the nodes a snapshot has emitted. -/
def Found (snapshot : Snapshot Node Node) (state : X) : Prop :=
  ∃ event ∈ snapshot.events, presentation.denote event.value state

/-- A run of a plan from the seeds. -/
def runFrom (scheduler : Scheduler Node) (fuel : Nat) : Snapshot Node Node :=
  run presentation.system scheduler fuel (initial presentation.seeds)

variable {presentation}

/-! ## Generated nodes describe exactly the states that reach the goal -/

theorem generated_sound {node : Node} (generated : Generated presentation.system presentation.seeds node) :
    ∀ state, presentation.denote node state → Reaches span goal state := by
  induction generated with
  | root member =>
    intro state holds
    exact .goal ((presentation.seeds_exact state).mpr ⟨_, member, holds⟩)
  | successor _ child ih =>
    intro state holds
    obtain ⟨event, starts, inside⟩ := presentation.predecessors_sound _ _ child state holds
    rw [← starts]
    exact .step event (ih _ inside)

variable (presentation) in
/-- Every generated node is good. -/
def AllGood : Prop := ∀ node, Generated presentation.system presentation.seeds node → presentation.good node

theorem generated_complete (allGood : presentation.AllGood) {state : X} (reaches : Reaches span goal state) :
    ∃ node, Generated presentation.system presentation.seeds node ∧ presentation.denote node state := by
  induction reaches with
  | goal atGoal =>
    obtain ⟨node, member, holds⟩ := (presentation.seeds_exact _).mp atGoal
    exact ⟨node, .root member, holds⟩
  | step event _ ih =>
    obtain ⟨node, generated, holds⟩ := ih
    rcases presentation.predecessors_complete node (allGood node generated) (span.source event)
        ⟨event, rfl, holds⟩ with same | ⟨previous, member, denotes⟩
    · exact ⟨node, generated, same⟩
    · exact ⟨previous, .successor generated member, denotes⟩

/-! ## Plans -/

/-- **Every run is sound.** -/
theorem found_sound (scheduler : Scheduler Node) (fuel : Nat) {state : X}
    (found : presentation.Found (presentation.runFrom scheduler fuel) state) : Reaches span goal state := by
  obtain ⟨event, member, holds⟩ := found
  obtain ⟨generated, emitted⟩ :=
    (sound_run presentation.system scheduler (initial_sound presentation.system presentation.seeds) fuel).2
      event member
  have same : event.value = event.origin := (Option.some.inj emitted).symm
  rw [same] at holds
  exact generated_sound generated _ holds

/-- **Every fair plan is complete** when every generated node is good. -/
theorem fair_complete (allGood : presentation.AllGood) {scheduler : Scheduler Node}
    (fair : FairFrom presentation.system scheduler presentation.seeds) {state : X}
    (reaches : Reaches span goal state) : ∃ fuel, presentation.Found (presentation.runFrom scheduler fuel) state := by
  obtain ⟨node, generated, holds⟩ := generated_complete allGood reaches
  obtain ⟨fuel, member⟩ :=
    fair_emits_reachable presentation.system scheduler presentation.seeds fair generated
      (show presentation.system.emit node = some node from rfl)
  exact ⟨fuel, _, member, holds⟩

theorem fair_exact (allGood : presentation.AllGood) {scheduler : Scheduler Node}
    (fair : FairFrom presentation.system scheduler presentation.seeds) (state : X) :
    Reaches span goal state ↔ ∃ fuel, presentation.Found (presentation.runFrom scheduler fuel) state :=
  ⟨fair_complete allGood fair, fun ⟨fuel, found⟩ => found_sound scheduler fuel found⟩

/-- **All fair plans find the same states.** -/
theorem fair_plans_agree (allGood : presentation.AllGood) {first second : Scheduler Node}
    (firstFair : FairFrom presentation.system first presentation.seeds)
    (secondFair : FairFrom presentation.system second presentation.seeds) (state : X) :
    (∃ fuel, presentation.Found (presentation.runFrom first fuel) state) ↔
      ∃ fuel, presentation.Found (presentation.runFrom second fuel) state :=
  (fair_exact allGood firstFair state).symm.trans (fair_exact allGood secondFair state)

/-- **Breadth-first search is exact.** -/
theorem breadthFirst_exact [DecidableEq Node] (allGood : presentation.AllGood) (state : X) :
    Reaches span goal state ↔
      ∃ fuel, presentation.Found (presentation.runFrom Scheduler.breadthFirst fuel) state :=
  fair_exact allGood (breadthFirst_fair presentation.system presentation.seeds) state

/-! ## Levels and the initial chain -/

variable (presentation) in
/-- The nodes expanded at each depth: the seeds, then the predecessors of the previous level. -/
def level : Nat → List Node
  | 0 => presentation.seeds
  | count + 1 => (level count).flatMap presentation.predecessors

/-- **Level `n` describes the states `n` steps before the goal**, for an exact presentation. -/
theorem level_denotes (exact : ∀ node state,
      (∃ previous ∈ presentation.predecessors node, presentation.denote previous state) ↔
        derivedDiamond span (presentation.denote node) state) : ∀ (count : Nat) (state : X),
    (∃ node ∈ presentation.level count, presentation.denote node state) ↔
      (derivedDiamond span)^[count] goal state
  | 0, state => (presentation.seeds_exact state).symm
  | count + 1, state => by
    rw [Function.iterate_succ_apply']
    constructor
    · rintro ⟨node, member, holds⟩
      obtain ⟨parent, parentMember, child⟩ := List.mem_flatMap.mp member
      obtain ⟨event, starts, inside⟩ := (exact parent state).mp ⟨node, child, holds⟩
      exact ⟨event, starts, (level_denotes exact count _).mp ⟨parent, parentMember, inside⟩⟩
    · rintro ⟨event, starts, inside⟩
      obtain ⟨parent, parentMember, parentHolds⟩ := (level_denotes exact count _).mpr inside
      obtain ⟨node, child, holds⟩ := (exact parent state).mpr ⟨event, starts, parentHolds⟩
      exact ⟨node, List.mem_flatMap.mpr ⟨parent, parentMember, child⟩, holds⟩

theorem chain_iff_iterate : ∀ (count : Nat) (state : X),
    chain span goal count state ↔ ∃ depth < count, (derivedDiamond span)^[depth] goal state
  | 0, _ => by simp [chain]
  | count + 1, state => by
    change goal state ∨ derivedDiamond span (chain span goal count) state ↔ _
    constructor
    · rintro (atGoal | ⟨event, starts, inside⟩)
      · exact ⟨0, Nat.zero_lt_succ _, atGoal⟩
      · obtain ⟨depth, below, holds⟩ := (chain_iff_iterate count _).mp inside
        refine ⟨depth + 1, Nat.succ_lt_succ below, ?_⟩
        rw [Function.iterate_succ_apply']
        exact ⟨event, starts, holds⟩
    · rintro ⟨depth, below, holds⟩
      cases depth with
      | zero => exact Or.inl holds
      | succ depth =>
        rw [Function.iterate_succ_apply'] at holds
        obtain ⟨event, starts, inside⟩ := holds
        exact Or.inr ⟨event, starts,
          (chain_iff_iterate count _).mpr ⟨depth, Nat.lt_of_succ_lt_succ below, inside⟩⟩

/-- **The levels describe the initial chain**: for an exact presentation, the first `n` levels
describe its `n`-th stage. -/
theorem levels_denote_chain (exact : ∀ node state,
      (∃ previous ∈ presentation.predecessors node, presentation.denote previous state) ↔
        derivedDiamond span (presentation.denote node) state) (count : Nat) (state : X) :
    (∃ depth < count, ∃ node ∈ presentation.level depth, presentation.denote node state) ↔
      chain span goal count state := by
  rw [chain_iff_iterate]
  exact exists_congr fun depth => and_congr_right fun _ => level_denotes exact depth state

/-! ## Saturation -/

variable (presentation) in
/-- Every seed, and every predecessor of an emitted node, was emitted or is still live. -/
def Closed (snapshot : Snapshot Node Node) : Prop :=
  (∀ seed ∈ presentation.seeds, (∃ event ∈ snapshot.events, event.value = seed) ∨ seed ∈ snapshot.frontier) ∧
    (∀ event ∈ snapshot.events, ∀ previous ∈ presentation.predecessors event.value,
      (∃ other ∈ snapshot.events, other.value = previous) ∨ previous ∈ snapshot.frontier) ∧
    (∀ event ∈ snapshot.events, event.value = event.origin)

theorem closed_initial : presentation.Closed (initial presentation.seeds) :=
  ⟨fun _ member => Or.inr member, fun _ member => by simp [initial] at member,
    fun _ member => by simp [initial] at member⟩

theorem closed_tick (scheduler : Scheduler Node) {snapshot : Snapshot Node Node}
    (closed : presentation.Closed snapshot) :
    presentation.Closed (tick presentation.system scheduler snapshot) := by
  obtain ⟨seedsClosed, eventsClosed, values⟩ := closed
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil =>
    simp only [tick, ordered]
    exact ⟨seedsClosed, eventsClosed, values⟩
  | cons node pending =>
    have liveSplit : ∀ live ∈ snapshot.frontier, live = node ∨ live ∈ pending := by
      intro live member
      have reordered := (scheduler.mem_reorder_iff).mpr member
      rw [ordered] at reordered
      simpa using reordered
    have newEvents : (tick presentation.system scheduler snapshot).events =
        snapshot.events ++ [⟨node, node⟩] := by
      simp only [tick, ordered]
      rfl
    have newFrontier : (tick presentation.system scheduler snapshot).frontier =
        scheduler.integrate pending (presentation.predecessors node) := by
      simp only [tick, ordered]
      rfl
    have keep : ∀ live, ((∃ event ∈ snapshot.events, event.value = live) ∨ live ∈ snapshot.frontier) →
        (∃ event ∈ (tick presentation.system scheduler snapshot).events, event.value = live) ∨
          live ∈ (tick presentation.system scheduler snapshot).frontier := by
      intro live old
      rw [newEvents, newFrontier]
      rcases old with ⟨event, member, same⟩ | member
      · exact Or.inl ⟨event, List.mem_append_left _ member, same⟩
      · rcases liveSplit live member with rfl | pendingMember
        · exact Or.inl ⟨⟨live, live⟩, by simp, rfl⟩
        · exact Or.inr ((scheduler.mem_integrate_iff).mpr (Or.inl pendingMember))
    refine ⟨fun seed member => keep seed (seedsClosed seed member), ?_, ?_⟩
    · intro event member previous previousMember
      rw [newEvents] at member
      rcases List.mem_append.mp member with old | new
      · exact keep previous (eventsClosed event old previous previousMember)
      · simp only [List.mem_singleton] at new
        subst new
        rw [newFrontier]
        exact Or.inr ((scheduler.mem_integrate_iff).mpr (Or.inr previousMember))
    · intro event member
      rw [newEvents] at member
      rcases List.mem_append.mp member with old | new
      · exact values event old
      · simp only [List.mem_singleton] at new
        subst new
        rfl

theorem closed_runFrom (scheduler : Scheduler Node) :
    ∀ fuel, presentation.Closed (presentation.runFrom scheduler fuel)
  | 0 => closed_initial
  | fuel + 1 => closed_tick scheduler (closed_runFrom scheduler fuel)

/-- **Saturation is a certificate**: when every emitted node is good and every live node's states
are already described by emitted nodes, the emitted nodes describe exactly the states that reach
the goal, whatever the plan. -/
theorem saturated_exact (scheduler : Scheduler Node) (fuel : Nat)
    (emittedGood : ∀ event ∈ (presentation.runFrom scheduler fuel).events, presentation.good event.value)
    (covered : ∀ node ∈ (presentation.runFrom scheduler fuel).frontier, ∀ state,
      presentation.denote node state → presentation.Found (presentation.runFrom scheduler fuel) state)
    (state : X) :
    Reaches span goal state ↔ presentation.Found (presentation.runFrom scheduler fuel) state := by
  refine ⟨fun reaches => ?_, found_sound scheduler fuel⟩
  obtain ⟨seedsClosed, eventsClosed, _⟩ := closed_runFrom (presentation := presentation) scheduler fuel
  have emittedOrLive : ∀ node, ((∃ event ∈ (presentation.runFrom scheduler fuel).events, event.value = node) ∨
      node ∈ (presentation.runFrom scheduler fuel).frontier) →
      ∀ state, presentation.denote node state → presentation.Found (presentation.runFrom scheduler fuel) state := by
    rintro node (⟨event, member, rfl⟩ | live) state holds
    · exact ⟨event, member, holds⟩
    · exact covered node live state holds
  refine reaches_least (closed := presentation.Found (presentation.runFrom scheduler fuel)) ?_ state reaches
  intro state holds
  rcases holds with atGoal | ⟨event, starts, ⟨emitted, member, inside⟩⟩
  · obtain ⟨seed, seedMember, seedHolds⟩ := (presentation.seeds_exact state).mp atGoal
    exact emittedOrLive seed (seedsClosed seed seedMember) state seedHolds
  · rcases presentation.predecessors_complete emitted.value (emittedGood emitted member) state
        ⟨event, starts, inside⟩ with same | ⟨previous, previousMember, previousHolds⟩
    · exact ⟨emitted, member, same⟩
    · exact emittedOrLive previous (eventsClosed emitted member previous previousMember) state previousHolds

/-! ## Reading a run -/

/-- A decidable, sound covering test between node descriptions, and a decidable test of goodness. -/
structure Covering (presentation : Presentation span goal Node) where
  covers : Node → List Node → Bool
  sound : ∀ node others, covers node others = true →
    ∀ state, presentation.denote node state → ∃ other ∈ others, presentation.denote other state
  isGood : Node → Bool
  isGood_sound : ∀ node, isGood node = true → presentation.good node

/-- Every emitted node is good, and every live node is covered by the emitted nodes. -/
def saturated (covering : Covering presentation) (snapshot : Snapshot Node Node) : Bool :=
  (snapshot.events.all fun event => covering.isGood event.value) &&
    snapshot.frontier.all fun node => covering.covers node (snapshot.events.map (·.value))

theorem good_of_saturated (covering : Covering presentation) {snapshot : Snapshot Node Node}
    (done : saturated covering snapshot = true) : ∀ event ∈ snapshot.events, presentation.good event.value :=
  fun event member => covering.isGood_sound _ (List.all_eq_true.mp (Bool.and_eq_true_iff.mp done).1 event member)

theorem covered_of_saturated (covering : Covering presentation) {scheduler : Scheduler Node} {fuel : Nat}
    (done : saturated covering (presentation.runFrom scheduler fuel) = true) :
    ∀ node ∈ (presentation.runFrom scheduler fuel).frontier, ∀ state,
      presentation.denote node state → presentation.Found (presentation.runFrom scheduler fuel) state := by
  intro node live state holds
  obtain ⟨other, member, otherHolds⟩ :=
    covering.sound node _ (List.all_eq_true.mp (Bool.and_eq_true_iff.mp done).2 node live) state holds
  obtain ⟨event, eventMember, rfl⟩ := List.mem_map.mp member
  exact ⟨event, eventMember, otherHolds⟩

/-- What a run says about one state. -/
inductive Answer where
  | reaches
  | cannotReach
  | unknown
  deriving DecidableEq, Repr

variable (presentation) in
/-- **Read a run**: the state is described by an emitted node, or the run is saturated and it is
not, or neither. -/
def answer (scheduler : Scheduler Node) (covering : Covering presentation) (member : Node → X → Bool)
    (fuel : Nat) (state : X) : Answer :=
  if ((presentation.runFrom scheduler fuel).events.any fun event => member event.value state) then .reaches
  else if saturated covering (presentation.runFrom scheduler fuel) then .cannotReach
  else .unknown

variable {member : Node → X → Bool}

/-- **`reaches` is sound** when the membership test is sound. -/
theorem answer_reaches (sound : ∀ node state, member node state = true → presentation.denote node state)
    {scheduler : Scheduler Node} {covering : Covering presentation} {fuel : Nat} {state : X}
    (read : presentation.answer scheduler covering member fuel state = .reaches) : Reaches span goal state := by
  unfold answer at read
  split_ifs at read with emitted
  obtain ⟨event, eventMember, holds⟩ := List.any_eq_true.mp emitted
  exact found_sound scheduler fuel ⟨event, eventMember, sound _ _ holds⟩

/-- **`cannotReach` is sound** when the membership test is complete at the state asked about. -/
theorem answer_cannotReach {state : X} (complete : ∀ node, presentation.denote node state → member node state = true)
    {scheduler : Scheduler Node} {covering : Covering presentation} {fuel : Nat}
    (read : presentation.answer scheduler covering member fuel state = .cannotReach) :
    ¬ Reaches span goal state := by
  unfold answer at read
  split_ifs at read with emitted done
  intro reaches
  obtain ⟨event, eventMember, holds⟩ :=
    (saturated_exact scheduler fuel (good_of_saturated covering done) (covered_of_saturated covering done)
      state).mp reaches
  exact emitted (List.any_eq_true.mpr ⟨event, eventMember, complete _ holds⟩)

/-- **Fair plans eventually answer `reaches`** for every state that reaches the goal, when every
generated node is good. -/
theorem answer_complete (exact : ∀ node state, member node state = true ↔ presentation.denote node state)
    (allGood : presentation.AllGood) {scheduler : Scheduler Node}
    (fair : FairFrom presentation.system scheduler presentation.seeds)
    (covering : Covering presentation) {state : X} (reaches : Reaches span goal state) :
    ∃ fuel, presentation.answer scheduler covering member fuel state = .reaches := by
  obtain ⟨fuel, event, eventMember, holds⟩ := fair_complete allGood fair reaches
  refine ⟨fuel, ?_⟩
  unfold answer
  rw [if_pos (List.any_eq_true.mpr ⟨event, eventMember, (exact _ _).mpr holds⟩)]


end Presentation

end Mettapedia.OSLF.Framework.BackwardSearch
