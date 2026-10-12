import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Policies
import Mettapedia.GSLT.Dynamics.ContextualControlSurface

/-!
# The merge of independent proposals is an order-free merge of deltas

`GSLT.Dynamics.ContextualDeltaHandlers` lets a branch carry a delta, and merges
the deltas of unordered alternatives through an `AlternativeMerge`: a resolver
that may refuse, and that carries, as a field, the proof that it does not depend
on the order of the alternatives.

Here that proof is not a field to supply.  A **footprinted delta**
(`FootprintedDelta`) is a partial change of a located state certified at a read
and a written footprint.  Footprinted deltas compose (`FootprintedDelta.seq`),
and two independent ones commute (`FootprintedDelta.seq_comm_of_independent`).
So the merge that puts independent deltas one after another, and refuses any
list with two deltas that are not independent, is an `AlternativeMerge`
(`waveMerge`): its order-freedom is the frame law.

* `deltaAlgebra`: footprinted deltas act on states that may have been refused,
  as a `DeltaAlgebra`.
* `Proposal.delta`: the delta of a proposal is the publication of its steps at
  its footprint.
* `waveMerge_proposals`: merging the deltas of proposals is publishing them all
  when they are independent in pairs, and a refusal otherwise.
* `publishWave_change_eq_merge`: the wave policy of `Regions.Policies` is this
  merge, applied to the enclosing state.
* `Policy.ofResolution`: the three resolutions of
  `GSLT.Dynamics.ContextualControlSurface.ResolutionPolicy`, as policies at the
  observation of a region.  To retain is to publish nothing; to select the first
  is to publish the chosen one (`Policy.ofResolution_select_zero`); to merge
  through `waveMerge` is the wave policy (`Policy.ofResolution_merge_wave`); and
  every merge is a function of the bag of outcomes
  (`Policy.ofResolution_merge_orderFree`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers (DeltaAlgebra AlternativeMerge)
open Mettapedia.GSLT.Dynamics.ContextualControlSurface (ResolutionPolicy)

universe u v w

/-- **A footprinted delta**: a partial change of a located state, certified at
the locations it reads and the locations it writes. -/
@[ext] structure FootprintedDelta (Location : Type u) (Value : Type v) [DecidableEq Location]
    where
  /-- The locations the change reads. -/
  reads : Finset Location
  /-- The locations the change writes. -/
  writes : Finset Location
  /-- The change; `none` is a refusal. -/
  act : (Location → Value) → Option (Location → Value)
  /-- The change is certified at its footprint. -/
  certified : EffectFootprinted (fun source target => act source = some target) reads writes

variable {Location : Type u} {Value : Type v} {Answer : Type w}

namespace FootprintedDelta

variable [DecidableEq Location]

/-- The delta that changes nothing and reads nothing. -/
def empty : FootprintedDelta Location Value where
  reads := ∅
  writes := ∅
  act := some
  certified := by
    constructor
    · intro source target same location _
      cases same
      rfl
    · intro source target same framedSource _
      cases same
      exact ⟨framedSource, rfl,
        fun location inside => absurd inside (Finset.notMem_empty location), fun _ _ => rfl⟩

/-- One delta after another: it reads what either reads and writes what either
writes. -/
def seq (first second : FootprintedDelta Location Value) : FootprintedDelta Location Value where
  reads := first.reads ∪ second.reads
  writes := first.writes ∪ second.writes
  act state := (first.act state).bind second.act
  certified := by
    have composed := comp_effectFootprinted first.certified second.certified
    constructor
    · intro source target fired
      exact composed.preserves (Option.bind_eq_some_iff.mp fired)
    · intro source target fired framedSource agrees
      obtain ⟨framedTarget, framedFired, written, outside⟩ :=
        composed.frame (Option.bind_eq_some_iff.mp fired) framedSource agrees
      exact ⟨framedTarget, Option.bind_eq_some_iff.mpr framedFired, written, outside⟩

theorem seq_assoc (first second third : FootprintedDelta Location Value) :
    (first.seq second).seq third = first.seq (second.seq third) := by
  apply FootprintedDelta.ext
  · exact Finset.union_assoc _ _ _
  · exact Finset.union_assoc _ _ _
  · funext state
    exact Option.bind_assoc _ _ _

theorem empty_seq (delta : FootprintedDelta Location Value) : empty.seq delta = delta := by
  apply FootprintedDelta.ext
  · exact Finset.empty_union _
  · exact Finset.empty_union _
  · rfl

theorem seq_empty (delta : FootprintedDelta Location Value) : delta.seq empty = delta := by
  apply FootprintedDelta.ext
  · exact Finset.union_empty _
  · exact Finset.union_empty _
  · funext state
    show (delta.act state).bind some = delta.act state
    cases delta.act state <;> rfl

/-- **Independent deltas**: the writes of each meet neither the reads nor the
writes of the other. -/
def Independent (first second : FootprintedDelta Location Value) : Prop :=
  IndependentEffects first.reads first.writes second.reads second.writes

instance decidableIndependent (first second : FootprintedDelta Location Value) :
    Decidable (first.Independent second) :=
  inferInstanceAs
    (Decidable (IndependentEffects first.reads first.writes second.reads second.writes))

theorem Independent.symm {first second : FootprintedDelta Location Value}
    (independent : first.Independent second) : second.Independent first :=
  independentEffects_symm independent

/-- **Independent deltas commute**: either order is the same delta. -/
theorem seq_comm_of_independent {first second : FootprintedDelta Location Value}
    (independent : first.Independent second) : first.seq second = second.seq first := by
  apply FootprintedDelta.ext
  · exact Finset.union_comm _ _
  · exact Finset.union_comm _ _
  · funext state
    exact bind_comm_of_independent first.certified second.certified independent state

/-- The deltas of a list, one after another. -/
def seqAll : List (FootprintedDelta Location Value) → FootprintedDelta Location Value :=
  List.foldr seq empty

/-- **Deltas that are independent in pairs compose to one delta in every
order.** -/
theorem seqAll_perm {deltas reordered : List (FootprintedDelta Location Value)}
    (perm : deltas.Perm reordered) (independent : deltas.Pairwise Independent) :
    seqAll deltas = seqAll reordered := by
  induction perm with
  | nil => rfl
  | cons delta _ ih =>
      show delta.seq (seqAll _) = delta.seq (seqAll _)
      rw [ih (List.pairwise_cons.mp independent).2]
  | swap first second rest =>
      show second.seq (first.seq (seqAll rest)) = first.seq (second.seq (seqAll rest))
      rw [← seq_assoc, ← seq_assoc,
        seq_comm_of_independent ((List.pairwise_cons.mp independent).1 first List.mem_cons_self)]
  | trans firstPerm _ ihFirst ihSecond =>
      rw [ihFirst independent,
        ihSecond ((firstPerm.pairwise_iff Independent.symm).mp independent)]

end FootprintedDelta

section Merge

variable [DecidableEq Location]

/-- **The merge of a wave**: deltas that are independent in pairs are put one
after another; any other list is refused.  That it does not depend on the order
of the deltas is proved, from the footprints. -/
def waveMerge : AlternativeMerge (FootprintedDelta Location Value) where
  merge deltas :=
    if deltas.Pairwise FootprintedDelta.Independent then some (FootprintedDelta.seqAll deltas)
    else none
  permutationInvariant := by
    intro first second perm
    by_cases independent : first.Pairwise FootprintedDelta.Independent
    · rw [if_pos independent,
        if_pos ((perm.pairwise_iff FootprintedDelta.Independent.symm).mp independent),
        FootprintedDelta.seqAll_perm perm independent]
    · rw [if_neg independent, if_neg fun reorderedIndependent =>
        independent
          ((perm.pairwise_iff FootprintedDelta.Independent.symm).mpr reorderedIndependent)]

/-- **Footprinted deltas act on states that may have been refused.**  The state
`none` is the refusal; it stays refused. -/
def deltaAlgebra : DeltaAlgebra (Option (Location → Value)) (FootprintedDelta Location Value) where
  empty := FootprintedDelta.empty
  compose := FootprintedDelta.seq
  apply state delta := state.bind delta.act
  compose_assoc := FootprintedDelta.seq_assoc
  empty_compose := FootprintedDelta.empty_seq
  compose_empty := FootprintedDelta.seq_empty
  apply_empty state := by cases state <;> rfl
  apply_compose state first second := (Option.bind_assoc state first.act second.act).symm

end Merge

section Proposals

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- **The delta of a proposal**: the publication of its steps, at its footprint. -/
def Proposal.delta (proposal : Proposal Location Value Answer) :
    FootprintedDelta Location Value where
  reads := proposal.reads
  writes := proposal.writes
  act := publish proposal.steps
  certified :=
    effectFootprinted_mono_reads (publish_effectFootprinted proposal.steps) Finset.subset_union_left

/-- Putting the deltas of proposals one after another is publishing them all. -/
theorem seqAll_delta_act (proposals : List (Proposal Location Value Answer)) :
    (FootprintedDelta.seqAll (proposals.map Proposal.delta)).act = publishAll proposals := by
  induction proposals with
  | nil => rfl
  | cons proposal rest ih =>
      funext world
      show (publish proposal.steps world).bind
          (FootprintedDelta.seqAll (rest.map Proposal.delta)).act = _
      rw [ih, publishAll_cons]

/-- **The merge of the deltas of proposals** is the publication of all of them
when they are independent in pairs, and a refusal otherwise. -/
theorem waveMerge_proposals (proposals : List (Proposal Location Value Answer))
    (world : Location → Value) :
    (waveMerge.merge (proposals.map Proposal.delta)).bind (fun delta => delta.act world) =
      if proposals.Pairwise Proposal.Independent then publishAll proposals world else none := by
  have same : (proposals.map Proposal.delta).Pairwise FootprintedDelta.Independent ↔
      proposals.Pairwise Proposal.Independent :=
    List.pairwise_map
  show (if (proposals.map Proposal.delta).Pairwise FootprintedDelta.Independent then
      some (FootprintedDelta.seqAll (proposals.map Proposal.delta)) else none).bind
        (fun delta => delta.act world) = _
  by_cases independent : proposals.Pairwise Proposal.Independent
  · rw [if_pos (same.mpr independent), if_pos independent, Option.bind_some, seqAll_delta_act]
  · rw [if_neg (fun mapped => independent (same.mp mapped)), if_neg independent]
    rfl

/-- **The wave policy is the merge of the deltas of the proposals**, applied to
the enclosing state. -/
theorem publishWave_change_eq_merge (outcomes : List (Answer × Proposal Location Value Answer))
    (world : Location → Value) :
    Policy.publishWave.change outcomes world =
      (waveMerge.merge ((outcomes.map Prod.snd).map Proposal.delta)).bind
        (fun delta => delta.act world) :=
  (waveMerge_proposals (outcomes.map Prod.snd) world).symm

/-- **The policy of a resolution.**  `ContextualControlSurface.ResolutionPolicy`
names the three things an observer may ask of isolated worlds: to retain them, to
select one by its position, or to merge their deltas through a resolver.  This is
what each does at the observation of a region, the deltas being those of the
proposals. -/
def Policy.ofResolution :
    ResolutionPolicy (FootprintedDelta Location Value) → Policy Location Value Answer
  | .retain => Policy.publishNone
  | .select index => Policy.publishChosenBy fun outcomes => outcomes[index]?
  | .merge resolver =>
      { returned := fun outcomes => outcomes.map Prod.fst
        change := fun outcomes world =>
          (resolver.merge (outcomes.map fun outcome => outcome.2.delta)).bind fun delta =>
            delta.act world }

/-- Selecting the first world is publishing the chosen one. -/
theorem Policy.ofResolution_select_zero :
    Policy.ofResolution (.select 0) = (Policy.publishChosen : Policy Location Value Answer) := by
  show Policy.publishChosenBy (fun outcomes => outcomes[0]?) = Policy.publishChosenBy List.head?
  congr 1
  funext outcomes
  exact List.head?_eq_getElem?.symm

/-- **Merging through the merge of a wave is the wave policy.** -/
theorem Policy.ofResolution_merge_wave :
    Policy.ofResolution (.merge waveMerge) =
      (Policy.publishWave : Policy Location Value Answer) := by
  show (⟨fun outcomes => outcomes.map Prod.fst, _⟩ : Policy Location Value Answer) =
    ⟨fun outcomes => outcomes.map Prod.fst, _⟩
  congr 1
  funext outcomes world
  have merged := waveMerge_proposals (outcomes.map Prod.snd) world
  rw [List.map_map] at merged
  exact merged

/-- **Every merge is a function of the bag of outcomes**, whatever its resolver:
the resolver does not depend on the order of the deltas. -/
theorem Policy.ofResolution_merge_orderFree
    (resolver : AlternativeMerge (FootprintedDelta Location Value)) :
    (Policy.ofResolution (.merge resolver) : Policy Location Value Answer).OrderFree := by
  intro outcomes reordered perm
  refine ⟨perm.map _, ?_⟩
  funext world
  show (resolver.merge (outcomes.map fun outcome => outcome.2.delta)).bind _ =
    (resolver.merge (reordered.map fun outcome => outcome.2.delta)).bind _
  rw [resolver.permutationInvariant (perm.map fun outcome => outcome.2.delta)]

end Proposals

/-! ## Controls -/

namespace Controls

/-- **Positive**: the deltas of two proposals that share a read and write apart
are merged, in both orders, to one delta. -/
theorem shared_gate_deltas_merge :
    (waveMerge.merge [gatedAddToSpace.delta, gatedAnswer.delta]).isSome = true ∧
      waveMerge.merge [gatedAddToSpace.delta, gatedAnswer.delta] =
        waveMerge.merge [gatedAnswer.delta, gatedAddToSpace.delta] :=
  ⟨by decide, waveMerge.permutationInvariant (List.Perm.swap _ _ [])⟩

/-- **Negative**: the deltas of two takers of a token are refused. -/
theorem takers_deltas_refused :
    (waveMerge.merge [takeToken.delta, takeToken.delta]).isSome = false := by
  decide

end Controls

#print axioms FootprintedDelta.seq_assoc
#print axioms FootprintedDelta.seq_comm_of_independent
#print axioms FootprintedDelta.seqAll_perm
#print axioms waveMerge
#print axioms deltaAlgebra
#print axioms seqAll_delta_act
#print axioms waveMerge_proposals
#print axioms publishWave_change_eq_merge
#print axioms Policy.ofResolution_select_zero
#print axioms Policy.ofResolution_merge_wave
#print axioms Policy.ofResolution_merge_orderFree
#print axioms Controls.shared_gate_deltas_merge
#print axioms Controls.takers_deltas_refused

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
