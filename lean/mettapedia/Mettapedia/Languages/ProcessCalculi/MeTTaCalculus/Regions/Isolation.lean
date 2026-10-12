import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Modes

/-!
# Frame and isolation in the branch-local mode; their failure in the committed mode

**Frame.**  The outcomes of a branch-local region depend only on the snapshot
restricted to what the region reads and writes (`Region.branchLocal_congr`); the
outcome of one alternative depends only on what that alternative reads and
writes (`Proposal.outcome?_congr`).  A branch-local run returns no state: it
changes none.

**Isolation.**  The outcomes of a region are those of each of its alternatives
run alone from the same snapshot (`Region.branchLocal_eq_flatMap`), and the
outcomes of siblings are those of each sibling run alone
(`Region.branchLocal_alternatives`).  So the bag of outcomes, and with it the bag
of answers, is the same for every order of the siblings
(`Region.branchLocal_alternatives_perm`, `Region.answers_alternatives_perm`).

**The committed mode breaks both.**  That the order of alternatives is
observable under a shared state is known of the free computation with choice and
state (`ContextualEffectHandlers.Canary.shared_choice_order_is_observable`); the
instances below are that fact for additions to a space and for a sibling that
fails.  `SharedSpace` has two siblings that add an atom to one space and then
read the space.  Run in the committed mode, the two orders of the siblings return
two different bags of answers
(`SharedSpace.committed_bags_differ`), so no law makes committed answers
independent of sibling order (`SharedSpace.committed_not_order_independent`), and
a sibling does not have the answer it has alone
(`SharedSpace.committed_sibling_not_alone`).  In the branch-local mode the same
two siblings return one bag in both orders (`SharedSpace.branchLocal_answers`,
`SharedSpace.branchLocal_bags_agree`).
`FailedSibling` has a sibling that adds an atom and then fails: in the committed
mode its atom stays in the state (`FailedSibling.committed_keeps_failed_effect`);
in the branch-local mode it proposes nothing, and publishing what was proposed
leaves the state without it (`FailedSibling.branchLocal_drops_failed_effect`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

section Frame

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

theorem Proposal.reads_cons (first : Step Location Value)
    (proposal : Proposal Location Value Answer) :
    (proposal.cons first).reads = first.rule.reads ∪ proposal.reads := by
  simp [Proposal.reads, Proposal.cons, stepsReads, Finset.union_assoc]

theorem Proposal.writes_cons (first : Step Location Value)
    (proposal : Proposal Location Value Answer) :
    (proposal.cons first).writes = first.rule.writes ∪ proposal.writes :=
  rfl

/-- An alternative reads no more than its region. -/
theorem Region.reads_subset_of_mem {region : Region Location Value Answer}
    {proposal : Proposal Location Value Answer} (member : proposal ∈ region.proposals) :
    proposal.reads ⊆ region.reads := by
  induction region generalizing proposal with
  | fail => cases member
  | answer readout =>
      rw [Region.proposals, List.mem_singleton] at member
      subst member
      simp [Proposal.reads, stepsReads, Region.reads]
  | step first rest ih =>
      rw [Region.proposals, List.mem_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      rw [Proposal.reads_cons, Region.reads]
      exact Finset.union_subset_union (Finset.Subset.refl _) (ih innerMember)
  | orElse left right ihLeft ihRight =>
      rw [Region.proposals, List.mem_append] at member
      rw [Region.reads]
      rcases member with inLeft | inRight
      · exact (ihLeft inLeft).trans Finset.subset_union_left
      · exact (ihRight inRight).trans Finset.subset_union_right

/-- An alternative writes no more than its region. -/
theorem Region.writes_subset_of_mem {region : Region Location Value Answer}
    {proposal : Proposal Location Value Answer} (member : proposal ∈ region.proposals) :
    proposal.writes ⊆ region.writes := by
  induction region generalizing proposal with
  | fail => cases member
  | answer readout =>
      rw [Region.proposals, List.mem_singleton] at member
      subst member
      simp [Proposal.writes, stepsWrites, Region.writes]
  | step first rest ih =>
      rw [Region.proposals, List.mem_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      rw [Proposal.writes_cons, Region.writes]
      exact Finset.union_subset_union (Finset.Subset.refl _) (ih innerMember)
  | orElse left right ihLeft ihRight =>
      rw [Region.proposals, List.mem_append] at member
      rw [Region.writes]
      rcases member with inLeft | inRight
      · exact (ihLeft inLeft).trans Finset.subset_union_left
      · exact (ihRight inRight).trans Finset.subset_union_right

/-- **Frame, for one alternative.**  Its outcome, the answer and the proposal or
the lack of one, is the same from every two snapshots that agree on what it
reads and writes. -/
theorem Proposal.outcome?_congr (proposal : Proposal Location Value Answer)
    {source framed : Location → Value}
    (agrees : AgreesOn (proposal.reads ∪ proposal.writes) source framed) :
    proposal.outcome? source = proposal.outcome? framed := by
  have stepsAgree :
      AgreesOn (stepsReads proposal.steps ∪ stepsWrites proposal.steps) source framed :=
    agreesOn_mono
      (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)) agrees
  unfold Proposal.outcome?
  cases published : publish proposal.steps source with
  | none => rw [publish_eq_none_of_agreesOn stepsAgree published]
  | some view =>
      obtain ⟨framedView, framedPublished, written, outside⟩ :=
        (publish_effectFootprinted proposal.steps).frame published framed stepsAgree
      have preserved := (publish_effectFootprinted proposal.steps).preserves published
      have sameAnswer : proposal.readout.value view = proposal.readout.value framedView := by
        apply proposal.readout.value_local
        intro location inside
        by_cases isWritten : location ∈ stepsWrites proposal.steps
        · exact written location isWritten
        · rw [preserved location isWritten, outside location isWritten]
          exact agrees location (Finset.mem_union_left _ (Finset.mem_union_right _ inside))
      rw [framedPublished, Option.map_some, Option.map_some, sameAnswer]

/-- **Frame.**  The outcomes of a branch-local region are the same from every
two snapshots that agree on what the region reads and writes. -/
theorem Region.branchLocal_congr (region : Region Location Value Answer)
    {source framed : Location → Value}
    (agrees : AgreesOn (region.reads ∪ region.writes) source framed) :
    region.branchLocal source = region.branchLocal framed := by
  rw [Region.branchLocal_eq_filterMap, Region.branchLocal_eq_filterMap]
  apply List.filterMap_congr
  intro proposal member
  exact proposal.outcome?_congr
    (agreesOn_mono
      (Finset.union_subset_union (Region.reads_subset_of_mem member)
        (Region.writes_subset_of_mem member)) agrees)

/-! ## Isolation -/

/-- **Isolation, inside a region.**  The outcomes of a region are those of each
of its alternatives run alone from the same snapshot. -/
theorem Region.branchLocal_eq_flatMap (region : Region Location Value Answer)
    (snapshot : Location → Value) :
    region.branchLocal snapshot =
      region.proposals.flatMap fun proposal => proposal.region.branchLocal snapshot := by
  rw [Region.branchLocal_eq_filterMap]
  induction region.proposals with
  | nil => rfl
  | cons proposal rest ih =>
      rw [List.flatMap_cons, ← ih, Proposal.region_branchLocal]
      cases explored : proposal.outcome? snapshot <;> simp [explored]

/-- The region whose alternatives are the given siblings, in order. -/
def Region.alternatives :
    List (Region Location Value Answer) → Region Location Value Answer :=
  List.foldr Region.orElse Region.fail

/-- **Isolation, among siblings.**  The outcomes of sibling regions from one
snapshot are those of each sibling run alone from it. -/
theorem Region.branchLocal_alternatives (siblings : List (Region Location Value Answer))
    (snapshot : Location → Value) :
    (Region.alternatives siblings).branchLocal snapshot =
      siblings.flatMap fun sibling => sibling.branchLocal snapshot := by
  induction siblings with
  | nil => rfl
  | cons sibling rest ih =>
      show (Region.orElse sibling (Region.alternatives rest)).branchLocal snapshot = _
      rw [Region.branchLocal, ih, List.flatMap_cons]

/-- **The bag of outcomes is the same for every order of the siblings.** -/
theorem Region.branchLocal_alternatives_perm
    {siblings reordered : List (Region Location Value Answer)}
    (perm : siblings.Perm reordered) (snapshot : Location → Value) :
    ((Region.alternatives siblings).branchLocal snapshot).Perm
      ((Region.alternatives reordered).branchLocal snapshot) := by
  rw [Region.branchLocal_alternatives, Region.branchLocal_alternatives]
  exact perm.flatMap_right _

/-- **And so is the bag of answers.** -/
theorem Region.answers_alternatives_perm
    {siblings reordered : List (Region Location Value Answer)}
    (perm : siblings.Perm reordered) (snapshot : Location → Value) :
    ((((Region.alternatives siblings).branchLocal snapshot).map Prod.fst : List Answer) :
        Multiset Answer) =
      (((Region.alternatives reordered).branchLocal snapshot).map Prod.fst : List Answer) :=
  Multiset.coe_eq_coe.mpr ((Region.branchLocal_alternatives_perm perm snapshot).map _)

end Frame

/-! ## The committed mode: answers that depend on the order of siblings -/

namespace SharedSpace

/-- The atoms the two siblings add. -/
inductive Seen where
  | a
  | b
  deriving DecidableEq

/-- One shared space, empty. -/
def empty : Network Unit Seen := fun _ => 0

/-- A sibling: add an atom to the shared space, then read the space. -/
def sibling (atom : Seen) : Region Unit (Multiset Seen) (Multiset Seen) :=
  .step (Step.addAtom () atom) (.answer (Readout.valueAt ()))

/-- Run in the committed mode, the second sibling reads the first one's atom, in
either order, and both atoms stay in the space. -/
theorem committed_answers :
    ((Region.alternatives [sibling .a, sibling .b]).committed empty).1 = [{.a}, {.a, .b}] ∧
      ((Region.alternatives [sibling .b, sibling .a]).committed empty).1 = [{.b}, {.b, .a}] ∧
      ((Region.alternatives [sibling .a, sibling .b]).committed empty).2 () = {.a, .b} := by
  decide

/-- **The two orders of the siblings return two different bags of answers.** -/
theorem committed_bags_differ :
    (((Region.alternatives [sibling .a, sibling .b]).committed empty).1 :
        Multiset (Multiset Seen)) ≠
      ((Region.alternatives [sibling .b, sibling .a]).committed empty).1 := by
  decide

/-- **The committed mode breaks isolation**: no law makes the bag of committed
answers independent of the order of the siblings. -/
theorem committed_not_order_independent :
    ¬ ∀ siblings reordered : List (Region Unit (Multiset Seen) (Multiset Seen)),
      siblings.Perm reordered → ∀ world : Network Unit Seen,
        (((Region.alternatives siblings).committed world).1 : Multiset (Multiset Seen)) =
          ((Region.alternatives reordered).committed world).1 := fun law =>
  committed_bags_differ (law _ _ (List.Perm.swap _ _ []) empty)

/-- A sibling does not have the answer it has alone: alone the second sibling
reads its own atom only. -/
theorem committed_sibling_not_alone :
    ((sibling .b).committed empty).1 = [{.b}] ∧
      ((Region.alternatives [sibling .a, sibling .b]).committed empty).1 ≠
        ((sibling .a).committed empty).1 ++ ((sibling .b).committed empty).1 := by
  decide

/-- In the branch-local mode each sibling reads its own atom only, in both
orders. -/
theorem branchLocal_answers :
    ((Region.alternatives [sibling .a, sibling .b]).branchLocal empty).map Prod.fst =
        [{.a}, {.b}] ∧
      ((Region.alternatives [sibling .b, sibling .a]).branchLocal empty).map Prod.fst =
        [{.b}, {.a}] := by
  decide

/-- The two orders return one bag: an instance of
`Region.answers_alternatives_perm`. -/
theorem branchLocal_bags_agree :
    ((((Region.alternatives [sibling .a, sibling .b]).branchLocal empty).map Prod.fst :
        List (Multiset Seen)) : Multiset (Multiset Seen)) =
      (((Region.alternatives [sibling .b, sibling .a]).branchLocal empty).map Prod.fst :
        List (Multiset Seen)) :=
  Region.answers_alternatives_perm (List.Perm.swap _ _ []) empty

end SharedSpace

/-! ## The committed mode: the effect of a sibling that fails remains -/

namespace FailedSibling

/-- The atoms the two siblings add, and their answers. -/
inductive Tried where
  | a
  | b
  deriving DecidableEq

/-- One shared space, empty. -/
def empty : Network Unit Tried := fun _ => 0

/-- Add an atom to the shared space, then fail. -/
def failing : Region Unit (Multiset Tried) Tried :=
  .step (Step.addAtom () .a) .fail

/-- Add an atom to the shared space, then answer. -/
def succeeding : Region Unit (Multiset Tried) Tried :=
  .step (Step.addAtom () .b) (.answer (Readout.const .b))

/-- **In the committed mode the atom of the sibling that failed stays**: one
answer, two atoms. -/
theorem committed_keeps_failed_effect :
    ((Region.alternatives [failing, succeeding]).committed empty).1 = [.b] ∧
      ((Region.alternatives [failing, succeeding]).committed empty).2 () = {.a, .b} := by
  decide

/-- **In the branch-local mode the sibling that failed proposes nothing**: there
is one outcome, and publishing its proposal on the snapshot leaves the atom of the
sibling that answered and no other. -/
theorem branchLocal_drops_failed_effect :
    failing.branchLocal empty = [] ∧
      ((Region.alternatives [failing, succeeding]).branchLocal empty).map
          (fun outcome => (outcome.1, (publish outcome.2.steps empty).map fun world => world ())) =
        [(.b, some {.b})] := by
  decide

end FailedSibling

#print axioms Proposal.outcome?_congr
#print axioms Region.branchLocal_congr
#print axioms Region.branchLocal_eq_flatMap
#print axioms Region.branchLocal_alternatives
#print axioms Region.branchLocal_alternatives_perm
#print axioms Region.answers_alternatives_perm
#print axioms SharedSpace.committed_answers
#print axioms SharedSpace.committed_bags_differ
#print axioms SharedSpace.committed_not_order_independent
#print axioms SharedSpace.committed_sibling_not_alone
#print axioms SharedSpace.branchLocal_answers
#print axioms SharedSpace.branchLocal_bags_agree
#print axioms FailedSibling.committed_keeps_failed_effect
#print axioms FailedSibling.branchLocal_drops_failed_effect

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
