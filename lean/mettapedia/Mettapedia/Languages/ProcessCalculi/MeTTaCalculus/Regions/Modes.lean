import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Steps

/-!
# Regions and their two modes

A **region** is a finite program of local rule instances with answers: it fails,
or answers by reading the state, or fires one instance and goes on, or offers two
alternatives.  Each alternative of a region is a child region.

A region runs in one of two modes.  They are the two handlers that
`GSLT.Dynamics.ContextualEffectHandlers` gives one free computation with choice
and state, the shared one and the isolated one, on computations whose every
write is an instance of a local rule (`Regions.Handlers`).

* **Committed** (`Region.committed`).  Every step acts on the shared state at once.
  The second alternative starts from the state the first one left, and the steps
  of an alternative that fails later stay.  The run returns the answers and the
  state.
* **Branch-local** (`Region.branchLocal`).  The region runs on a private view of a
  snapshot: a step reads the view and writes the view, and the two alternatives
  start from one view.  The run returns **outcomes** and no state.  An outcome is
  an answer with a **proposal** (`Proposal`): the steps the alternative fired, in
  order, each with what it read, consumed and produced, and the readout that gave
  the answer.

Results.

* `Region.branchLocal_eq_filterMap`: the outcomes of a region from a snapshot are
  those of its alternatives (`Region.proposals`), each alone: an alternative has
  its outcome exactly when its steps can be published on the snapshot.
* `Proposal.modes_agree`: **for one region alone the two modes agree.**  The region
  of one alternative (`Proposal.region`) has its outcome from a snapshot, and
  publishing the proposal on the unchanged snapshot is the committed run: the same
  answer and the same state.  `Region.committed_of_mem_branchLocal` says it of
  every outcome of every region.
* `Proposal.refused_in_both_modes`: an alternative whose steps cannot be published
  answers in neither mode.  The modes differ in what it leaves:
  `Controls.failed_alternative_leaves_its_step` against
  `Controls.failed_alternative_has_no_outcome`.

What the syntax does not have: a step is an instance, so what it writes does not
depend on what an earlier step of the same alternative read.  A rule that writes
a function of a value it reads is one instance for each value, offered as
alternatives.  That is exact in the branch-local mode, where the alternatives see
one snapshot and one of them fires.  In the committed mode a later alternative
sees the write of an earlier one, so the alternatives together are not the rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

/-! ## Readouts -/

/-- **A readout**: an answer computed from the state at finitely many declared
locations. -/
structure Readout (Location : Type u) (Value : Type v) (Answer : Type w)
    [DecidableEq Location] where
  /-- The locations the answer may depend on. -/
  reads : Finset Location
  /-- The answer, from a state. -/
  value : (Location → Value) → Answer
  /-- The answer sees nothing outside the declared locations. -/
  value_local : ∀ {source framed : Location → Value},
    AgreesOn reads source framed → value source = value framed

namespace Readout

variable [DecidableEq Location]

/-- The answer that reads nothing. -/
def const (answer : Answer) : Readout Location Value Answer :=
  ⟨∅, fun _ => answer, fun _ => rfl⟩

/-- The value at one location. -/
def valueAt (location : Location) : Readout Location Value Value :=
  ⟨{location}, fun state => state location,
    fun agrees => agrees location (Finset.mem_singleton_self location)⟩

end Readout

/-! ## Regions and proposals -/

/-- **A region**: a finite program of local rule instances with answers. -/
inductive Region (Location : Type u) (Value : Type v) (Answer : Type w) [DecidableEq Location]
    [Zero Value] [Add Value] [SepAlgebra Value] : Type (max u v w) where
  /-- No answer. -/
  | fail : Region Location Value Answer
  /-- Answer by reading the state. -/
  | answer (readout : Readout Location Value Answer) : Region Location Value Answer
  /-- Fire one rule instance, then go on; no answer if it does not fire. -/
  | step (first : Step Location Value) (rest : Region Location Value Answer) :
      Region Location Value Answer
  /-- Two alternatives, in the order of evaluation. -/
  | orElse (left right : Region Location Value Answer) : Region Location Value Answer

/-- **A proposal**: one alternative of a region as it ran.  `steps` are the rule
instances it fired, in order, each with what it read, consumed and produced;
`readout` is how it read its answer. -/
structure Proposal (Location : Type u) (Value : Type v) (Answer : Type w)
    [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value] where
  /-- The rule instances fired, in order. -/
  steps : List (Step Location Value)
  /-- How the answer was read. -/
  readout : Readout Location Value Answer

section Runs

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

namespace Proposal

/-- The alternative with one more step in front. -/
def cons (first : Step Location Value) (proposal : Proposal Location Value Answer) :
    Proposal Location Value Answer :=
  ⟨first :: proposal.steps, proposal.readout⟩

/-- What a proposal read besides what it wrote: the locations its guards read
and the locations its answer read. -/
def reads (proposal : Proposal Location Value Answer) : Finset Location :=
  stepsReads proposal.steps ∪ proposal.readout.reads

/-- The locations a proposal changes. -/
def writes (proposal : Proposal Location Value Answer) : Finset Location :=
  stepsWrites proposal.steps

/-- The region that has this one alternative: its steps in order, then its
readout. -/
def region (proposal : Proposal Location Value Answer) : Region Location Value Answer :=
  proposal.steps.foldr Region.step (Region.answer proposal.readout)

/-- The outcome of an alternative from a snapshot: its steps are published on the
snapshot, privately, and the answer is read from the result. -/
def outcome? (proposal : Proposal Location Value Answer) (snapshot : Location → Value) :
    Option (Answer × Proposal Location Value Answer) :=
  (publish proposal.steps snapshot).map fun view => (proposal.readout.value view, proposal)

end Proposal

namespace Region

/-- **The branch-local run** from a snapshot.  A step reads and writes the private
view; both alternatives start from one view.  It returns the outcomes, each an
answer with its proposal, and no state. -/
def branchLocal : Region Location Value Answer → (Location → Value) →
    List (Answer × Proposal Location Value Answer)
  | fail, _ => []
  | answer readout, view => [(readout.value view, ⟨[], readout⟩)]
  | step first rest, view =>
      match first.fire view with
      | none => []
      | some next => (rest.branchLocal next).map fun outcome => (outcome.1, outcome.2.cons first)
  | orElse left right, view => left.branchLocal view ++ right.branchLocal view

/-- **The committed run** on the shared state.  A step changes the state at once;
the second alternative starts from the state the first one left; a step that
does not fire ends its alternative and leaves the state as it then is.  It returns
the answers and the state. -/
def committed : Region Location Value Answer → (Location → Value) →
    List Answer × (Location → Value)
  | fail, world => ([], world)
  | answer readout, world => ([readout.value world], world)
  | step first rest, world =>
      match first.fire world with
      | none => ([], world)
      | some next => rest.committed next
  | orElse left right, world =>
      ((left.committed world).1 ++ (right.committed (left.committed world).2).1,
        (right.committed (left.committed world).2).2)

/-- The alternatives of a region that end in an answer, in the order of
evaluation. -/
def proposals : Region Location Value Answer → List (Proposal Location Value Answer)
  | fail => []
  | answer readout => [⟨[], readout⟩]
  | step first rest => rest.proposals.map (Proposal.cons first)
  | orElse left right => left.proposals ++ right.proposals

/-- What the guards and the answers of a region may read. -/
def reads : Region Location Value Answer → Finset Location
  | fail => ∅
  | answer readout => readout.reads
  | step first rest => first.rule.reads ∪ rest.reads
  | orElse left right => left.reads ∪ right.reads

/-- What the steps of a region may change. -/
def writes : Region Location Value Answer → Finset Location
  | fail => ∅
  | answer _ => ∅
  | step first rest => first.rule.writes ∪ rest.writes
  | orElse left right => left.writes ∪ right.writes

end Region

/-! ## The outcomes are those of the alternatives -/

theorem Proposal.outcome?_eq_some_iff {proposal : Proposal Location Value Answer}
    {snapshot : Location → Value} {outcome : Answer × Proposal Location Value Answer} :
    proposal.outcome? snapshot = some outcome ↔
      ∃ view, publish proposal.steps snapshot = some view ∧
        (proposal.readout.value view, proposal) = outcome :=
  Option.map_eq_some_iff

theorem Proposal.outcome?_cons (first : Step Location Value)
    (proposal : Proposal Location Value Answer) (snapshot : Location → Value) :
    (proposal.cons first).outcome? snapshot =
      (first.fire snapshot).bind fun view =>
        (proposal.outcome? view).map fun outcome => (outcome.1, outcome.2.cons first) := by
  cases fired : first.fire snapshot with
  | none => simp [Proposal.outcome?, Proposal.cons, fired]
  | some view => simp [Proposal.outcome?, Proposal.cons, fired, Function.comp_def]

/-- **The outcomes of a region are those of its alternatives, each alone**: an
alternative has its outcome exactly when its steps can be published on the
snapshot. -/
theorem Region.branchLocal_eq_filterMap (region : Region Location Value Answer)
    (snapshot : Location → Value) :
    region.branchLocal snapshot =
      region.proposals.filterMap fun proposal => proposal.outcome? snapshot := by
  induction region generalizing snapshot with
  | fail => rfl
  | answer readout => rfl
  | step first rest ih =>
      rw [Region.branchLocal, Region.proposals, List.filterMap_map]
      cases fired : first.fire snapshot with
      | none => simp [Proposal.outcome?_cons, fired]
      | some view =>
          simp only [Function.comp_def, Proposal.outcome?_cons, fired, Option.bind_some]
          rw [ih view, List.map_filterMap]
  | orElse left right ihLeft ihRight =>
      rw [Region.branchLocal, Region.proposals, List.filterMap_append, ihLeft, ihRight]

/-- An outcome of a region is the outcome of one of its alternatives, and its
proposal is that alternative. -/
theorem Region.mem_branchLocal_iff {region : Region Location Value Answer}
    {snapshot : Location → Value} {outcome : Answer × Proposal Location Value Answer} :
    outcome ∈ region.branchLocal snapshot ↔
      outcome.2 ∈ region.proposals ∧ outcome.2.outcome? snapshot = some outcome := by
  rw [Region.branchLocal_eq_filterMap, List.mem_filterMap]
  constructor
  · rintro ⟨proposal, member, explored⟩
    obtain ⟨view, -, rfl⟩ := Proposal.outcome?_eq_some_iff.mp explored
    exact ⟨member, explored⟩
  · rintro ⟨member, explored⟩
    exact ⟨outcome.2, member, explored⟩

/-! ## One region alone -/

/-- The region of one alternative has that alternative and no other. -/
theorem Proposal.region_proposals (proposal : Proposal Location Value Answer) :
    proposal.region.proposals = [proposal] := by
  obtain ⟨steps, readout⟩ := proposal
  induction steps with
  | nil => rfl
  | cons first rest ih =>
      show (Region.step first (Proposal.region ⟨rest, readout⟩)).proposals = _
      rw [Region.proposals, ih]
      rfl

/-- Its branch-local run has the outcome of the alternative, or none. -/
theorem Proposal.region_branchLocal (proposal : Proposal Location Value Answer)
    (snapshot : Location → Value) :
    proposal.region.branchLocal snapshot = (proposal.outcome? snapshot).toList := by
  rw [Region.branchLocal_eq_filterMap, Proposal.region_proposals]
  cases explored : proposal.outcome? snapshot <;> simp [explored]

/-- Its committed run, when the steps can be published, is the publication. -/
theorem Proposal.region_committed (proposal : Proposal Location Value Answer)
    {snapshot view : Location → Value} (published : publish proposal.steps snapshot = some view) :
    proposal.region.committed snapshot = ([proposal.readout.value view], view) := by
  obtain ⟨steps, readout⟩ := proposal
  induction steps generalizing snapshot with
  | nil =>
      cases published
      rfl
  | cons first rest ih =>
      simp only [publish_cons, Option.bind_eq_some_iff] at published
      obtain ⟨middle, fired, restPublished⟩ := published
      show (Region.step first (Proposal.region ⟨rest, readout⟩)).committed snapshot = _
      simp only [Region.committed, fired]
      exact ih restPublished

/-- **The two modes agree for one region alone.**  When the steps of the one
alternative can be published on the snapshot, the branch-local run returns its
answer with the proposal, and the committed run returns the same answer and
leaves the state that publishing the proposal on the unchanged snapshot gives. -/
theorem Proposal.modes_agree (proposal : Proposal Location Value Answer)
    {snapshot view : Location → Value} (published : publish proposal.steps snapshot = some view) :
    proposal.region.branchLocal snapshot = [(proposal.readout.value view, proposal)] ∧
      proposal.region.committed snapshot = ([proposal.readout.value view], view) := by
  refine ⟨?_, proposal.region_committed published⟩
  rw [Proposal.region_branchLocal, Proposal.outcome?, published]
  rfl

/-- The same for every outcome of every region: publishing its proposal on the
unchanged snapshot succeeds, and is the committed run of that alternative alone,
with the answer of the outcome. -/
theorem Region.committed_of_mem_branchLocal {region : Region Location Value Answer}
    {snapshot : Location → Value} {outcome : Answer × Proposal Location Value Answer}
    (explored : outcome ∈ region.branchLocal snapshot) :
    ∃ view, publish outcome.2.steps snapshot = some view ∧
      outcome.2.region.committed snapshot = ([outcome.1], view) := by
  obtain ⟨view, published, same⟩ :=
    Proposal.outcome?_eq_some_iff.mp (Region.mem_branchLocal_iff.mp explored).2
  refine ⟨view, published, ?_⟩
  rw [Proposal.region_committed _ published]
  exact congrArg (fun answer => ([answer], view)) (congrArg Prod.fst same)

/-- **An alternative whose steps cannot be published answers in neither mode.**
The branch-local run has no outcome, and the committed run returns no answer; the
state the committed run leaves is not said to be the snapshot. -/
theorem Proposal.refused_in_both_modes (proposal : Proposal Location Value Answer)
    {snapshot : Location → Value} (refused : publish proposal.steps snapshot = none) :
    proposal.region.branchLocal snapshot = [] ∧ (proposal.region.committed snapshot).1 = [] := by
  constructor
  · rw [Proposal.region_branchLocal, Proposal.outcome?, refused]
    rfl
  · obtain ⟨steps, readout⟩ := proposal
    induction steps generalizing snapshot with
    | nil => cases refused
    | cons first rest ih =>
        show ((Region.step first (Proposal.region ⟨rest, readout⟩)).committed snapshot).1 = _
        cases fired : first.fire snapshot with
        | none => simp only [Region.committed, fired]
        | some middle =>
            simp only [Region.committed, fired]
            apply ih
            simpa only [publish_cons, fired, Option.bind_some] using refused

end Runs

/-! ## Controls -/

namespace Controls

/-- Two stores. -/
inductive Store where
  | space
  | cell
  deriving DecidableEq

/-- The state with nothing in any store. -/
def empty : Network Store ℕ := fun _ => 0

/-- Add `7` to the space, then read the space. -/
def addThenRead : Region Store (Multiset ℕ) (Multiset ℕ) :=
  .step (Step.addAtom .space 7) (.answer (Readout.valueAt .space))

/-- Add `7` to the space, then take a `3` that is not there. -/
def addThenFail : Region Store (Multiset ℕ) (Multiset ℕ) :=
  .step (Step.addAtom .space 7)
    (.step (Step.removeAtom .space 3) (.answer (Readout.valueAt .space)))

/-- **Positive**: the branch-local run returns the answer the branch read after
its own write. -/
theorem addThenRead_outcome :
    (addThenRead.branchLocal empty).map Prod.fst = [{7}] := by
  decide

/-- And the committed run returns the same answer and leaves the atom. -/
theorem addThenRead_committed :
    (addThenRead.committed empty).1 = [{7}] ∧ (addThenRead.committed empty).2 .space = {7} := by
  decide

/-- **Negative**: an alternative that fails has no outcome, so no proposal. -/
theorem failed_alternative_has_no_outcome : addThenFail.branchLocal empty = [] := by
  decide

/-- In the committed mode it has no answer either, and the step it fired before
it failed stays in the state. -/
theorem failed_alternative_leaves_its_step :
    (addThenFail.committed empty).1 = [] ∧ (addThenFail.committed empty).2 .space = {7} := by
  decide

/-- **Positive**: the value at a location is a readout. -/
theorem valueAt_reads (state : Network Store ℕ) :
    (Readout.valueAt Store.space : Readout Store (Multiset ℕ) (Multiset ℕ)).value state =
      state .space :=
  rfl

/-- **Negative**: the value at a location is not a readout that reads nothing. -/
theorem valueAt_needs_its_read :
    ¬ ∃ readout : Readout Store (Multiset ℕ) (Multiset ℕ),
      readout.reads = ∅ ∧ readout.value = fun state => state .space := by
  rintro ⟨readout, noReads, same⟩
  have equal := readout.value_local (source := empty) (framed := Pi.single Store.space {7})
    (by rw [noReads]; exact fun location inside => absurd inside (Finset.notMem_empty location))
  rw [same] at equal
  exact absurd equal (by decide)

end Controls

#print axioms Region.branchLocal_eq_filterMap
#print axioms Region.mem_branchLocal_iff
#print axioms Proposal.region_proposals
#print axioms Proposal.region_branchLocal
#print axioms Proposal.region_committed
#print axioms Proposal.modes_agree
#print axioms Region.committed_of_mem_branchLocal
#print axioms Proposal.refused_in_both_modes
#print axioms Controls.addThenRead_outcome
#print axioms Controls.addThenRead_committed
#print axioms Controls.failed_alternative_has_no_outcome
#print axioms Controls.failed_alternative_leaves_its_step
#print axioms Controls.valueAt_needs_its_read

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
