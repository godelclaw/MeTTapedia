import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Isolation
import Mettapedia.Logic.EvidenceStateInsufficiency

/-!
# Branch-local observations as a count

A region whose alternatives each return an observation, run with
`Region.branchLocal` from one snapshot, returns a bag of observations. Folding
`Counts.revise` over that bag is a count state. That count is the count of the
committed runs of the same alternatives, each alone from the snapshot. It is the
count of the one committed run of those alternatives together when that run's
answers are the branch-local bag. Pure answers are that case. The region of
probe p1 (`SharedSpace`) is a case where the two counts differ.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Controls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.SharedSpace
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Logic.EvidenceStateInsufficiency

/-- The empty flag store. -/
def emptyFlag : Unit → Flag := fun _ => 0

theorem emptyFlag_lowered : emptyFlag () = Flag.lowered := rfl

theorem emptyFlag_not_raised : emptyFlag () ≠ Flag.raised := by
  decide

/-- One alternative that returns a Boolean observation and writes nothing. -/
def pureObservation (observation : Bool) : Region Unit Flag Bool :=
  .answer (Readout.const observation)

theorem pureObservation_returns (observation : Bool) :
    ((pureObservation observation).branchLocal emptyFlag).map Prod.fst = [observation] := rfl

theorem pureObservation_not_fail (observation : Bool) :
    pureObservation observation ≠ (Region.fail : Region Unit Flag Bool) := by
  intro same
  cases same

/-- Two pure observations, true and then false. -/
def purePair : Region Unit Flag Bool :=
  Region.alternatives [pureObservation true, pureObservation false]

theorem purePair_answers :
    ((purePair.branchLocal emptyFlag).map Prod.fst) = [true, false] ∧
      (purePair.committed emptyFlag).1 = [true, false] :=
  ⟨rfl, rfl⟩

theorem purePair_not_one :
    ((purePair.branchLocal emptyFlag).map Prod.fst) ≠ [true] := by
  decide

/-- The bag of observations a branch-local run returns. -/
def observationBag {Location : Type} {Value : Type} {Answer : Type}
    [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]
    (region : Region Location Value Answer) (snapshot : Location → Value) : List Answer :=
  (region.branchLocal snapshot).map Prod.fst

theorem observationBag_purePair : observationBag purePair emptyFlag = [true, false] := rfl

theorem observationBag_fail :
    observationBag (Region.fail : Region Unit Flag Bool) emptyFlag = [] ∧
      observationBag (Region.fail : Region Unit Flag Bool) emptyFlag ≠
        observationBag purePair emptyFlag := by
  decide

/-- Counting a bag of Boolean observations from an empty count. -/
def countObservations (observations : List Bool) : Counts :=
  observations.foldl Counts.revise ⟨0, 0⟩

theorem countObservations_one : countObservations [true] = ⟨1, 0⟩ := rfl

theorem countObservations_two_ne : countObservations [true, true] ≠ ⟨1, 0⟩ := by
  decide

theorem foldl_revise_pos (counts : Counts) (observations : List Bool) :
    (observations.foldl Counts.revise counts).pos =
      counts.pos + observations.count true := by
  induction observations generalizing counts with
  | nil => simp
  | cons head tail ih =>
    cases head with
    | false =>
      rw [List.foldl_cons]
      have start : counts.revise false = ⟨counts.pos, counts.neg + 1⟩ := by
        unfold Counts.revise
        rw [if_neg Bool.false_ne_true]
      rw [start, ih, show (⟨counts.pos, counts.neg + 1⟩ : Counts).pos = counts.pos from rfl,
        List.count_cons, show (false == true) = false from rfl, if_neg Bool.false_ne_true,
        Nat.add_zero]
    | true =>
      rw [List.foldl_cons]
      have start : counts.revise true = ⟨counts.pos + 1, counts.neg⟩ := by
        unfold Counts.revise
        rw [if_pos rfl]
      rw [start, ih, show (⟨counts.pos + 1, counts.neg⟩ : Counts).pos = counts.pos + 1 from rfl,
        List.count_cons, show (true == true) = true from rfl, if_pos rfl, Nat.add_assoc,
        Nat.add_comm 1]

theorem foldl_revise_neg (counts : Counts) (observations : List Bool) :
    (observations.foldl Counts.revise counts).neg =
      counts.neg + observations.count false := by
  induction observations generalizing counts with
  | nil => simp
  | cons head tail ih =>
    cases head with
    | false =>
      rw [List.foldl_cons]
      have start : counts.revise false = ⟨counts.pos, counts.neg + 1⟩ := by
        unfold Counts.revise
        rw [if_neg Bool.false_ne_true]
      rw [start, ih, show (⟨counts.pos, counts.neg + 1⟩ : Counts).neg = counts.neg + 1 from rfl,
        List.count_cons, show (false == false) = true from rfl, if_pos rfl, Nat.add_assoc,
        Nat.add_comm 1]
    | true =>
      rw [List.foldl_cons]
      have start : counts.revise true = ⟨counts.pos + 1, counts.neg⟩ := by
        unfold Counts.revise
        rw [if_pos rfl]
      rw [start, ih, show (⟨counts.pos + 1, counts.neg⟩ : Counts).neg = counts.neg from rfl,
        List.count_cons, show (true == false) = false from rfl, if_neg Bool.false_ne_true,
        Nat.add_zero]

theorem countObservations_pos (observations : List Bool) :
    (countObservations observations).pos = observations.count true := by
  simpa [countObservations] using foldl_revise_pos ⟨0, 0⟩ observations

theorem countObservations_neg (observations : List Bool) :
    (countObservations observations).neg = observations.count false := by
  simpa [countObservations] using foldl_revise_neg ⟨0, 0⟩ observations

/-- An outcome explored from the snapshot publishes on that snapshot, and the
committed run of that alternative alone returns the outcome's answer. -/
theorem branch_outcome_publishes {Location : Type} {Value : Type} {Answer : Type}
    [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]
    {region : Region Location Value Answer} {snapshot : Location → Value}
    {outcome : Answer × Proposal Location Value Answer}
    (explored : outcome ∈ region.branchLocal snapshot) :
    ∃ view, publish outcome.2.steps snapshot = some view ∧
      (outcome.2.region.committed snapshot).1 = [outcome.1] := by
  obtain ⟨view, published, committedRun⟩ := Region.committed_of_mem_branchLocal explored
  exact ⟨view, published, congrArg Prod.fst committedRun⟩

theorem flatMap_alone_eq_answers {Location : Type} {Value : Type} {Answer : Type}
    [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]
    (outcomes : List (Answer × Proposal Location Value Answer))
    (snapshot : Location → Value)
    (each : ∀ outcome ∈ outcomes, (outcome.2.region.committed snapshot).1 = [outcome.1]) :
    (outcomes.flatMap fun outcome => (outcome.2.region.committed snapshot).1) =
      outcomes.map Prod.fst := by
  induction outcomes with
  | nil => rfl
  | cons head tail ih =>
    rw [List.flatMap_cons, each head List.mem_cons_self, List.singleton_append, List.map_cons]
    exact congrArg (fun rest => head.1 :: rest)
      (ih fun outcome member => each outcome (List.mem_cons_of_mem head member))

/-- The answers of the committed runs of the branch-local alternatives, each
alone from the snapshot. -/
def aloneAnswers {Location : Type} {Value : Type} {Answer : Type}
    [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]
    (region : Region Location Value Answer) (snapshot : Location → Value) : List Answer :=
  (region.branchLocal snapshot).flatMap fun outcome =>
    (outcome.2.region.committed snapshot).1

theorem observationBag_eq_aloneAnswers {Location : Type} {Value : Type} {Answer : Type}
    [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]
    (region : Region Location Value Answer) (snapshot : Location → Value) :
    observationBag region snapshot = aloneAnswers region snapshot := by
  unfold observationBag aloneAnswers
  refine (flatMap_alone_eq_answers (region.branchLocal snapshot) snapshot ?_).symm
  intro outcome explored
  obtain ⟨_, _, answer⟩ := branch_outcome_publishes explored
  exact answer

theorem aloneAnswers_one :
    aloneAnswers (pureObservation true) emptyFlag = [true] := by
  rw [← observationBag_eq_aloneAnswers]
  simpa [observationBag] using pureObservation_returns true

theorem aloneAnswers_not_repeated :
    aloneAnswers (pureObservation true) emptyFlag ≠ [true, true] := by
  rw [aloneAnswers_one]
  decide

/-- **The branch-local count is the count of the alternatives run committed,
each alone.** -/
theorem branchLocal_count_eq_alone {Location : Type} {Value : Type}
    [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]
    (region : Region Location Value Bool) (snapshot : Location → Value) :
    countObservations (observationBag region snapshot) =
      countObservations (aloneAnswers region snapshot) := by
  rw [observationBag_eq_aloneAnswers]

/-- Pure answers write nothing, so the one committed run of the alternatives
together has the branch-local count. -/
theorem pure_count_eq_committed :
    countObservations (observationBag purePair emptyFlag) =
      countObservations (purePair.committed emptyFlag).1 := by
  rw [observationBag_purePair, purePair_answers.2]

/-- Whether a probe-p1 answer holds both atoms. -/
def seesBoth (answer : Multiset Seen) : Bool :=
  decide (Seen.a ∈ answer ∧ Seen.b ∈ answer)

theorem seesBoth_pair : seesBoth {.a, .b} = true := by
  decide

theorem seesBoth_singleton : seesBoth {.a} = false ∧ seesBoth {.b} = false := by
  decide

/-- **Probe p1.** The branch-local count of the two siblings is not the count of
their one committed run: the second sibling reads the first sibling's atom. -/
theorem probe_p1_count_ne_committed :
    countObservations
        ((observationBag (Region.alternatives [sibling .a, sibling .b]) empty).map seesBoth) ≠
      countObservations
        (((Region.alternatives [sibling .a, sibling .b]).committed empty).1.map seesBoth) := by
  have branch := branchLocal_answers.1
  have joint := committed_answers.1
  rw [observationBag, branch, joint]
  simp only [List.map_cons, List.map_nil, seesBoth_pair, seesBoth_singleton.1,
    seesBoth_singleton.2, countObservations, List.foldl_cons, List.foldl_nil, Counts.revise]
  decide

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder
