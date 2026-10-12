import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Distinction.CausalGluing

/-!
# Queryable revision theories

A queryable revision theory separates three pieces that are often hidden in
one host loop:

* a relation saying which revision events may change a world;
* proof-relevant histories and snapshots;
* observations of a world after those events.

The event relation is intentionally relational rather than a fixed strategy.
`StrongSquare` records literal agreement of the two event orders, while
`ObservedSquare` only requires agreement at one declared observer.  This is a
small common interface for world-model revision, reflective-space updates,
and later certified parallel realizations.
-/

namespace Mettapedia.GSLT.Dynamics.QueryRevision

universe uWorld uRevision uQuery uObservation uObserved

set_option linter.checkUnivs false in
/-- A relational world-revision theory equipped with read-only queries. The
four carrier universes are independent; the record inhabits their maximum. -/
structure Theory where
  World : Type uWorld
  Revision : Type uRevision
  Query : Type uQuery
  Observation : Type uObservation
  Step : Revision → World → World → Prop
  query : World → Query → Observation

namespace Theory

/-- A chronological sequence of named revision events. -/
inductive HistoryStep (theory : Theory) :
    List theory.Revision → theory.World → theory.World → Prop where
  | nil (world : theory.World) : HistoryStep theory [] world world
  | cons {revision : theory.Revision} {revisions : List theory.Revision}
      {source middle target : theory.World} :
      theory.Step revision source middle →
      HistoryStep theory revisions middle target →
      HistoryStep theory (revision :: revisions) source target

namespace HistoryStep

/-- One revision is a singleton history. -/
theorem single {theory : Theory} {revision : theory.Revision}
    {source target : theory.World}
    (step : theory.Step revision source target) :
    theory.HistoryStep [revision] source target :=
  .cons step (.nil target)

/-- Concatenating chronological histories composes their executions. -/
theorem append {theory : Theory}
    {first second : List theory.Revision}
    {source middle target : theory.World}
    (firstSteps : theory.HistoryStep first source middle)
    (secondSteps : theory.HistoryStep second middle target) :
    theory.HistoryStep (first ++ second) source target := by
  induction firstSteps with
  | nil => simpa using secondSteps
  | cons step rest inductionHypothesis =>
      exact .cons step (inductionHypothesis secondSteps)

/-- Two chronological steps retain their actual intermediate world. -/
theorem two_iff {theory : Theory} {first second : theory.Revision}
    {source target : theory.World} :
    theory.HistoryStep [first, second] source target ↔
      ∃ middle, theory.Step first source middle ∧ theory.Step second middle target := by
  constructor
  · intro steps
    cases steps with
    | cons firstStep remaining =>
      cases remaining with
      | cons secondStep empty =>
        cases empty
        exact ⟨_, firstStep, secondStep⟩
  · rintro ⟨middle, firstStep, secondStep⟩
    exact .cons firstStep (.single secondStep)

/-- Interchange of every actual two-step path lifts through an arbitrary
prefix and the same complete suffix. The event order changes explicitly;
this does not erase chronology, proof multiplicity or semantic coefficients. -/
theorem swap_adjacent {theory : Theory} {first second : theory.Revision}
    (interchange : ∀ {source middle target : theory.World},
      theory.Step first source middle → theory.Step second middle target →
        ∃ afterSecond, theory.Step second source afterSecond ∧
          theory.Step first afterSecond target)
    (preceding suffix : List theory.Revision) {source target : theory.World}
    (steps : theory.HistoryStep (preceding ++ first :: second :: suffix) source target) :
    theory.HistoryStep (preceding ++ second :: first :: suffix) source target := by
  induction preceding generalizing source with
  | nil =>
    cases steps with
    | cons firstStep remaining =>
      cases remaining with
      | cons secondStep continuation =>
        obtain ⟨afterSecond, secondFromSource, firstAfterSecond⟩ :=
          interchange firstStep secondStep
        exact .cons secondFromSource (.cons firstAfterSecond continuation)
  | cons revision preceding inductionHypothesis =>
    cases steps with
    | cons prefixStep continuation =>
      exact .cons prefixStep (inductionHypothesis continuation)

/-- The existing generated trace equivalence preserves every actual final
world when its permitted swaps have a symmetric actual-path interchange
law. This is equality of reachability relations, not derivation bags. -/
theorem traceEquiv_iff {theory : Theory}
    (independent : theory.Revision → theory.Revision → Prop)
    (symmetric : ∀ {first second}, independent first second → independent second first)
    (interchange : ∀ {first second : theory.Revision}
      {source middle target : theory.World}, independent first second →
      theory.Step first source middle → theory.Step second middle target →
        ∃ afterSecond, theory.Step second source afterSecond ∧
          theory.Step first afterSecond target)
    {first second : List theory.Revision}
    (equivalent : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv
      independent first second) (source target : theory.World) :
    theory.HistoryStep first source target ↔
      theory.HistoryStep second source target := by
  have same := Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv.invariant
    (fun events => theory.HistoryStep events source target)
    (fun preceding following a b related => propext
      ⟨swap_adjacent (interchange related) preceding following,
        swap_adjacent (interchange (symmetric related)) preceding following⟩)
    equivalent
  rw [same]


/-- A declared step invariant is retained by every actual complete history. -/
theorem observation_preserved {theory : Theory} {Observed : Type*}
    (observe : theory.World → Observed)
    (preserved : ∀ {event source target}, theory.Step event source target →
      observe target = observe source)
    {events : List theory.Revision} {source target : theory.World}
    (steps : theory.HistoryStep events source target) :
    observe target = observe source := by
  induction steps with
  | nil world => rfl
  | cons first rest inductionHypothesis =>
      exact inductionHypothesis.trans (preserved first)


end HistoryStep

/-- A snapshot retains its origin, chronological revision identity, current
world, and the derivation connecting them. -/
structure Snapshot (theory : Theory) where
  origin : theory.World
  revisions : List theory.Revision
  world : theory.World
  reaches : theory.HistoryStep revisions origin world

namespace Snapshot

/-- Every world has an initial, history-free snapshot. -/
def initial (theory : Theory) (world : theory.World) : theory.Snapshot where
  origin := world
  revisions := []
  world := world
  reaches := .nil world

/-- Extend a snapshot by one checked revision event. -/
def extend {theory : Theory} (snapshot : theory.Snapshot)
    (revision : theory.Revision) (target : theory.World)
    (step : theory.Step revision snapshot.world target) : theory.Snapshot where
  origin := snapshot.origin
  revisions := snapshot.revisions ++ [revision]
  world := target
  reaches := snapshot.reaches.append (.single step)

/-- Querying a snapshot is read-only by construction. -/
def query {theory : Theory} (snapshot : theory.Snapshot)
    (request : theory.Query) : theory.Observation :=
  theory.query snapshot.world request

end Snapshot

/-- A revision is enabled when it has at least one successor. -/
def Enabled (theory : Theory) (revision : theory.Revision)
    (source : theory.World) : Prop :=
  ∃ target, theory.Step revision source target

/-- A literal commuting square: both revision orders reach one common world. -/
structure StrongSquare (theory : Theory)
    (first second : theory.Revision) (source : theory.World) where
  afterFirst : theory.World
  afterSecond : theory.World
  joined : theory.World
  firstFromSource : theory.Step first source afterFirst
  secondFromSource : theory.Step second source afterSecond
  secondAfterFirst : theory.Step second afterFirst joined
  firstAfterSecond : theory.Step first afterSecond joined

/-- An observer-relative square: the two orders may retain different internal
world representations, but the explicitly named value observer cannot
distinguish their endpoints.  The complete query profile is one such value. -/
structure ObservedSquare (theory : Theory)
    (first second : theory.Revision) (source : theory.World)
    {Value : Type uObserved} (observe : theory.World → Value) where
  afterFirst : theory.World
  afterSecond : theory.World
  firstThenSecond : theory.World
  secondThenFirst : theory.World
  firstFromSource : theory.Step first source afterFirst
  secondFromSource : theory.Step second source afterSecond
  secondAfterFirst : theory.Step second afterFirst firstThenSecond
  firstAfterSecond : theory.Step first afterSecond secondThenFirst
  observationAgrees : observe firstThenSecond = observe secondThenFirst

namespace StrongSquare

/-- Literal state commutation implies commutation for every named value
observer. -/
def toObservedValue {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (square : theory.StrongSquare first second source)
    {Value : Type uObserved} (observe : theory.World → Value) :
    theory.ObservedSquare first second source observe where
  afterFirst := square.afterFirst
  afterSecond := square.afterSecond
  firstThenSecond := square.joined
  secondThenFirst := square.joined
  firstFromSource := square.firstFromSource
  secondFromSource := square.secondFromSource
  secondAfterFirst := square.secondAfterFirst
  firstAfterSecond := square.firstAfterSecond
  observationAgrees := rfl

/-- Literal state commutation preserves the complete query profile. -/
def toQuerySquare {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (square : theory.StrongSquare first second source) :
    theory.ObservedSquare first second source theory.query :=
  square.toObservedValue theory.query

end StrongSquare

/-- Strong coexecutibility retains a literal common residual. -/
def StronglyCoexecutible (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  Nonempty (theory.StrongSquare first second source)

/-- Query coexecutibility permits representation differences invisible to the
complete declared query profile. -/
def QueryCoexecutible (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  Nonempty (theory.ObservedSquare first second source theory.query)

/-- Every pair of actual initial successors admits a literal common residual.
This is stronger than the existence of one `StrongSquare`. It does not assert
equality of derivation bags, grades, or the order of recorded events. -/
def AllInitialOutcomesJoin (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  ∀ {afterFirst afterSecond : theory.World},
    theory.Step first source afterFirst →
    theory.Step second source afterSecond →
    ∃ joined, theory.Step second afterFirst joined ∧
      theory.Step first afterSecond joined

/-- Both revisions are enabled, and all their initial outcome pairs can
coexecute. Enablement rules out a vacuous admission of a disabled operation. -/
def AllOutcomeCoexecutible (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  theory.Enabled first source ∧ theory.Enabled second source ∧
    theory.AllInitialOutcomesJoin first second source

theorem AllInitialOutcomesJoin.symm {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (joins : theory.AllInitialOutcomesJoin first second source) :
    theory.AllInitialOutcomesJoin second first source := by
  intro afterSecond afterFirst secondStep firstStep
  obtain ⟨joined, secondAfterFirst, firstAfterSecond⟩ := joins firstStep secondStep
  exact ⟨joined, firstAfterSecond, secondAfterFirst⟩

theorem AllOutcomeCoexecutible.symm {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (coexecutible : theory.AllOutcomeCoexecutible first second source) :
    theory.AllOutcomeCoexecutible second first source :=
  ⟨coexecutible.2.1, coexecutible.1, AllInitialOutcomesJoin.symm coexecutible.2.2⟩

/-- An all-outcome contract constructs a square for the chosen actual
successors; neither initial successor is replaced by a convenient witness. -/
theorem AllInitialOutcomesJoin.square {theory : Theory}
    {first second : theory.Revision} {source afterFirst afterSecond : theory.World}
    (joins : theory.AllInitialOutcomesJoin first second source)
    (firstStep : theory.Step first source afterFirst)
    (secondStep : theory.Step second source afterSecond) :
    ∃ square : theory.StrongSquare first second source,
      square.afterFirst = afterFirst ∧ square.afterSecond = afterSecond := by
  obtain ⟨joined, secondAfterFirst, firstAfterSecond⟩ := joins firstStep secondStep
  exact ⟨{
    afterFirst := afterFirst
    afterSecond := afterSecond
    joined := joined
    firstFromSource := firstStep
    secondFromSource := secondStep
    secondAfterFirst := secondAfterFirst
    firstAfterSecond := firstAfterSecond }, rfl, rfl⟩

theorem AllOutcomeCoexecutible.stronglyCoexecutible {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (coexecutible : theory.AllOutcomeCoexecutible first second source) :
    theory.StronglyCoexecutible first second source := by
  obtain ⟨afterFirst, firstStep⟩ := coexecutible.1
  obtain ⟨afterSecond, secondStep⟩ := coexecutible.2.1
  obtain ⟨square, _, _⟩ := AllInitialOutcomesJoin.square coexecutible.2.2 firstStep secondStep
  exact ⟨square⟩

/-- For deterministic initial revisions, a constructed commuting square
covers every initial outcome. Uniqueness is an explicit hypothesis, not
inferred from a successful example or a scheduler's selected path. -/
theorem StrongSquare.allOutcomeCoexecutible {theory : Theory}
    {first second : theory.Revision} {source : theory.World}
    (square : theory.StrongSquare first second source)
    (firstUnique : ∀ {left right}, theory.Step first source left →
      theory.Step first source right → left = right)
    (secondUnique : ∀ {left right}, theory.Step second source left →
      theory.Step second source right → left = right) :
    theory.AllOutcomeCoexecutible first second source := by
  refine ⟨⟨square.afterFirst, square.firstFromSource⟩,
    ⟨square.afterSecond, square.secondFromSource⟩, ?_⟩
  intro afterFirst afterSecond firstStep secondStep
  have sameFirst := firstUnique firstStep square.firstFromSource
  have sameSecond := secondUnique secondStep square.secondFromSource
  refine ⟨square.joined, ?_, ?_⟩
  · simpa only [sameFirst] using square.secondAfterFirst
  · simpa only [sameSecond] using square.firstAfterSecond

/-- A common residual permits the same actual continuation in both orders.
The complete suffix is retained; no observer erasure or re-evaluation is used. -/
theorem StrongSquare.continue {theory : Theory}
    {first second : theory.Revision} {source target : theory.World}
    (square : theory.StrongSquare first second source)
    {suffix : List theory.Revision}
    (continuation : theory.HistoryStep suffix square.joined target) :
    theory.HistoryStep (first :: second :: suffix) source target ∧
      theory.HistoryStep (second :: first :: suffix) source target := by
  exact ⟨.cons square.firstFromSource (.cons square.secondAfterFirst continuation),
    .cons square.secondFromSource (.cons square.firstAfterSecond continuation)⟩

/-- Conflict means joint initial enablement without a literal commuting
square.  Observer-relative conflict remains a separate, weaker notion. -/
def Conflict (theory : Theory)
    (first second : theory.Revision) (source : theory.World) : Prop :=
  theory.Enabled first source ∧ theory.Enabled second source ∧
    ¬ theory.StronglyCoexecutible first second source

/-- Literal coexecution always gives query-relative coexecution. -/
theorem stronglyCoexecutible_implies_queryCoexecutible
    {theory : Theory} {first second : theory.Revision}
    {source : theory.World}
    (coexecutible : theory.StronglyCoexecutible first second source) :
    theory.QueryCoexecutible first second source := by
  rcases coexecutible with ⟨square⟩
  exact ⟨square.toQuerySquare⟩

end Theory

namespace Controls

/-- Each revision independently chooses one of two updates to its own
coordinate. Both are nondeterministic, and queries expose both coordinates. -/
def independentBranchingTheory : Theory where
  World := Nat × Nat
  Revision := Bool
  Query := Unit
  Observation := Nat × Nat
  Step revision source target :=
    if revision then
      target.2 = source.2 ∧
        (target.1 = source.1 + 1 ∨ target.1 = source.1 + 2)
    else
      target.1 = source.1 ∧
        (target.2 = source.2 + 3 ∨ target.2 = source.2 + 5)
  query world _ := world

theorem independent_nondeterministic_outcomes_coexecute (source : Nat × Nat) :
    independentBranchingTheory.AllOutcomeCoexecutible true false source := by
  refine ⟨⟨(source.1 + 1, source.2), ?_⟩,
    ⟨(source.1, source.2 + 3), ?_⟩, ?_⟩
  · simp [independentBranchingTheory]
  · simp [independentBranchingTheory]
  · intro afterFirst afterSecond firstStep secondStep
    change afterFirst.2 = source.2 ∧
      (afterFirst.1 = source.1 + 1 ∨ afterFirst.1 = source.1 + 2) at firstStep
    change afterSecond.1 = source.1 ∧
      (afterSecond.2 = source.2 + 3 ∨ afterSecond.2 = source.2 + 5) at secondStep
    refine ⟨(afterFirst.1, afterSecond.2), ?_, ?_⟩
    · change afterFirst.1 = afterFirst.1 ∧
        (afterSecond.2 = afterFirst.2 + 3 ∨ afterSecond.2 = afterFirst.2 + 5)
      exact ⟨rfl, by simpa only [firstStep.1] using secondStep.2⟩
    · change afterSecond.2 = afterSecond.2 ∧
        (afterFirst.1 = afterSecond.1 + 1 ∨ afterFirst.1 = afterSecond.1 + 2)
      exact ⟨rfl, by simpa only [secondStep.1] using firstStep.2⟩

/-- Preserve the chosen final world of an actual sequential path, including
each revision's nondeterministic choice. -/
theorem independent_branching_actual_steps_swap
    {source middle target : Nat × Nat}
    (firstStep : independentBranchingTheory.Step true source middle)
    (secondStep : independentBranchingTheory.Step false middle target) :
    ∃ afterSecond, independentBranchingTheory.Step false source afterSecond ∧
      independentBranchingTheory.Step true afterSecond target := by
  change middle.2 = source.2 ∧
    (middle.1 = source.1 + 1 ∨ middle.1 = source.1 + 2) at firstStep
  change target.1 = middle.1 ∧
    (target.2 = middle.2 + 3 ∨ target.2 = middle.2 + 5) at secondStep
  refine ⟨(source.1, target.2), ?_, ?_⟩
  · change source.1 = source.1 ∧
      (target.2 = source.2 + 3 ∨ target.2 = source.2 + 5)
    exact ⟨rfl, by simpa only [firstStep.1] using secondStep.2⟩
  · change target.2 = target.2 ∧
      (target.1 = source.1 + 1 ∨ target.1 = source.1 + 2)
    exact ⟨rfl, by simpa only [secondStep.1] using firstStep.2⟩

/-- The independent branching program retains every actual continuation
after swapping the two revisions inside any chronological context. -/
theorem independent_branching_history_swap
    (preceding suffix : List Bool) {source target : Nat × Nat}
    (steps : independentBranchingTheory.HistoryStep
      (preceding ++ true :: false :: suffix) source target) :
    independentBranchingTheory.HistoryStep
      (preceding ++ false :: true :: suffix) source target :=
  Theory.HistoryStep.swap_adjacent independent_branching_actual_steps_swap
    preceding suffix steps

/-- The reverse independent order preserves the actual choices as well. -/
theorem independent_branching_reverse_steps_swap
    {source middle target : Nat × Nat}
    (firstStep : independentBranchingTheory.Step false source middle)
    (secondStep : independentBranchingTheory.Step true middle target) :
    ∃ afterSecond, independentBranchingTheory.Step true source afterSecond ∧
      independentBranchingTheory.Step false afterSecond target := by
  change middle.1 = source.1 ∧
    (middle.2 = source.2 + 3 ∨ middle.2 = source.2 + 5) at firstStep
  change target.2 = middle.2 ∧
    (target.1 = middle.1 + 1 ∨ target.1 = middle.1 + 2) at secondStep
  refine ⟨(target.1, source.2), ?_, ?_⟩
  · change source.2 = source.2 ∧
      (target.1 = source.1 + 1 ∨ target.1 = source.1 + 2)
    exact ⟨rfl, by simpa only [firstStep.1] using secondStep.2⟩
  · change target.1 = target.1 ∧
      (target.2 = source.2 + 3 ∨ target.2 = source.2 + 5)
    exact ⟨rfl, by simpa only [secondStep.1] using firstStep.2⟩

/-- Distinct coordinate revisions admit each actual sequential swap. -/
theorem independent_branching_interchange {first second : Bool}
    {source middle target : Nat × Nat} (distinct : first ≠ second)
    (firstStep : independentBranchingTheory.Step first source middle)
    (secondStep : independentBranchingTheory.Step second middle target) :
    ∃ afterSecond, independentBranchingTheory.Step second source afterSecond ∧
      independentBranchingTheory.Step first afterSecond target := by
  cases first <;> cases second
  · exact False.elim (distinct rfl)
  · exact independent_branching_reverse_steps_swap firstStep secondStep
  · exact independent_branching_actual_steps_swap firstStep secondStep
  · exact False.elim (distinct rfl)

/-- Any finite sequence of the declared swaps retains every actual final
world of the nondeterministic coordinate program. -/
theorem independent_branching_trace_reaches_iff {first second : List Bool}
    (equivalent : Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv
      (· ≠ ·) first second) (source target : Nat × Nat) :
    independentBranchingTheory.HistoryStep first source target ↔
      independentBranchingTheory.HistoryStep second source target :=
  Theory.HistoryStep.traceEquiv_iff (theory := independentBranchingTheory) (· ≠ ·) Ne.symm
    independent_branching_interchange equivalent source target

theorem all_four_nondeterministic_pairs_retained :
    independentBranchingTheory.Step true (0, 0) (1, 0) ∧
    independentBranchingTheory.Step true (0, 0) (2, 0) ∧
    independentBranchingTheory.Step false (0, 0) (0, 3) ∧
    independentBranchingTheory.Step false (0, 0) (0, 5) ∧
    (∀ left ∈ ([1, 2] : List Nat), ∀ right ∈ ([3, 5] : List Nat),
      independentBranchingTheory.HistoryStep [true, false] (0, 0) (left, right) ∧
      independentBranchingTheory.HistoryStep [false, true] (0, 0) (left, right)) := by
  refine ⟨by simp [independentBranchingTheory], by simp [independentBranchingTheory],
    by simp [independentBranchingTheory], by simp [independentBranchingTheory], ?_⟩
  intro left leftChoice right rightChoice
  have l : left = 1 ∨ left = 2 := by simpa using leftChoice
  have r : right = 3 ∨ right = 5 := by simpa using rightChoice
  constructor
  · refine .cons (middle := (left, 0)) ?_
      (Theory.HistoryStep.single (theory := independentBranchingTheory)
        (revision := false) (source := (left, 0)) (target := (left, right)) ?_)
    · simpa [independentBranchingTheory] using l
    · simpa [independentBranchingTheory] using r
  · refine .cons (middle := (0, right)) ?_
      (Theory.HistoryStep.single (theory := independentBranchingTheory)
        (revision := true) (source := (0, right)) (target := (left, right)) ?_)
    · simpa [independentBranchingTheory] using r
    · simpa [independentBranchingTheory] using l

/-- Two revisions share a successful square, but one possible first-revision
successor cannot run the other revision. Queries expose the complete world. -/
def branchingTheory : Theory where
  World := Fin 4
  Revision := Bool
  Query := Unit
  Observation := Fin 4
  Step revision source target :=
    if revision then
      (source = 0 ∧ (target = 1 ∨ target = 2)) ∨
        (source = 1 ∧ target = 3)
    else
      (source = 0 ∧ target = 1) ∨ (source = 1 ∧ target = 3)
  query world _ := world

theorem some_initial_outcomes_coexecute :
    branchingTheory.StronglyCoexecutible true false (0 : Fin 4) := by
  exact ⟨{
    afterFirst := (1 : Fin 4)
    afterSecond := (1 : Fin 4)
    joined := (3 : Fin 4)
    firstFromSource := by simp [branchingTheory]
    secondFromSource := by simp [branchingTheory]
    secondAfterFirst := by simp [branchingTheory]
    firstAfterSecond := by simp [branchingTheory] }⟩

theorem other_initial_outcome_cannot_coexecute :
    ¬ branchingTheory.AllInitialOutcomesJoin true false (0 : Fin 4) := by
  intro joins
  obtain ⟨joined, secondAfterFirst, _⟩ :=
    joins (afterFirst := (2 : Fin 4)) (afterSecond := (1 : Fin 4))
      (by simp [branchingTheory]) (by simp [branchingTheory])
  simp [branchingTheory] at secondAfterFirst

theorem existential_square_is_not_all_outcome_permission :
    branchingTheory.StronglyCoexecutible true false (0 : Fin 4) ∧
      ¬ branchingTheory.AllOutcomeCoexecutible true false (0 : Fin 4) := by
  exact ⟨some_initial_outcomes_coexecute,
    fun coexecutible => other_initial_outcome_cannot_coexecute coexecutible.2.2⟩

/-- Initial choices have a common residual, but a later second-revision
choice reaches an additional world that the reverse order cannot reach. -/
def extraSequentialOutcomeTheory : Theory where
  World := Nat
  Revision := Bool
  Query := Unit
  Observation := Nat
  Step revision source target :=
    if revision then
      (source = 0 ∧ target = 1) ∨ (source = 2 ∧ target = 3)
    else
      (source = 0 ∧ target = 2) ∨ (source = 1 ∧ (target = 3 ∨ target = 4))
  query world _ := world

theorem all_initial_successors_join_with_extra_sequential_outcome :
    extraSequentialOutcomeTheory.AllOutcomeCoexecutible true false (0 : Nat) := by
  refine ⟨⟨(1 : Nat), by simp [extraSequentialOutcomeTheory]⟩,
    ⟨(2 : Nat), by simp [extraSequentialOutcomeTheory]⟩, ?_⟩
  intro afterFirst afterSecond firstStep secondStep
  have firstEqual : afterFirst = (1 : Nat) := by simpa [extraSequentialOutcomeTheory] using firstStep
  have secondEqual : afterSecond = (2 : Nat) := by simpa [extraSequentialOutcomeTheory] using secondStep
  subst afterFirst afterSecond
  exact ⟨(3 : Nat), by simp [extraSequentialOutcomeTheory], by simp [extraSequentialOutcomeTheory]⟩

/-- Universal initial squares do not imply preservation of all actual
sequential outcomes. The observer here reads the complete world. -/
theorem extra_sequential_outcome_cannot_reorder :
    extraSequentialOutcomeTheory.HistoryStep [true, false] (0 : Nat) (4 : Nat) ∧
      ¬ extraSequentialOutcomeTheory.HistoryStep [false, true] (0 : Nat) (4 : Nat) := by
  constructor
  · exact Theory.HistoryStep.two_iff.mpr
      ⟨(1 : Nat), by simp [extraSequentialOutcomeTheory], by simp [extraSequentialOutcomeTheory]⟩
  · intro reverse
    obtain ⟨middle, secondStep, firstStep⟩ := Theory.HistoryStep.two_iff.mp reverse
    have secondEqual : middle = (2 : Nat) := by simpa [extraSequentialOutcomeTheory] using secondStep
    subst middle
    simp [extraSequentialOutcomeTheory] at firstStep

end Controls

end Mettapedia.GSLT.Dynamics.QueryRevision
