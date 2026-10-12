import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.MonotoneFragment

/-!
# Compatible proposals: one notion of a wave, two tests for it

Independence by read and write sets and compatibility by deltas are two tests.
What both establish of a pair of proposals is one property (`Proposal.Compatible`):

* publishing either **preserves the outcomes** of the other
  (`Proposal.PreservesOutcomes`): an outcome the other has from a state, it still
  has from the state reached;
* from a state on which both publish, the two orders reach one state.

Results.

* `wave_of_compatible_every_order`: **outcomes explored from one state whose
  proposals are compatible in pairs are a wave.**  Every order of them is
  published from that state, each validated by replay when its turn comes; all
  orders reach one state; and every order is the committed run of the
  alternatives that answered, with the answers that were returned.
* `Proposal.Independent.compatible`: independence by read and write sets is a
  test for it.  `Proposal.DeltaCompatible.compatible`: for proposals that only
  add, compatibility by deltas is another.
* The property is asked of pairs, so **the two tests may be mixed in one wave**:
  `CompatibilityControls.mixed_wave` has a removal and two additions of one kind;
  the removal is independent of each addition by sets, the two additions are
  compatible by deltas and not independent by sets, and the three are published
  in every order to one state.  Neither test admits the three alone.
* `CompatibilityControls.not_compatible`: two takers of one token are not
  compatible: after either, the other has lost its outcome.

The property is asked of pairs and from every state.  Two removals of one kind
never have it, with however many occurrences; whether they are a wave depends on
the state and on how many they are, and is decided by counting
(`PatternFootprints.Claims`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra

universe u v w

variable {Location : Type u} {Value : Type v} {Answer : Type w}

section Compatibility

variable [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- Publishing `first` **preserves the outcomes** of `second`: an outcome that
`second` has from a state, it has from the state that `first` publishes to. -/
def Proposal.PreservesOutcomes (first second : Proposal Location Value Answer) : Prop :=
  ∀ ⦃state afterFirst : Location → Value⦄ ⦃outcome : Answer × Proposal Location Value Answer⦄,
    publish first.steps state = some afterFirst → second.outcome? state = some outcome →
      second.outcome? afterFirst = some outcome

/-- **Compatible proposals**: each preserves the outcomes of the other, and from
a state on which both publish the two orders reach one state. -/
structure Proposal.Compatible (first second : Proposal Location Value Answer) : Prop where
  preserves : first.PreservesOutcomes second
  preserved : second.PreservesOutcomes first
  joins : ∀ ⦃state afterFirst afterSecond forward reverse : Location → Value⦄,
    publish first.steps state = some afterFirst → publish second.steps state = some afterSecond →
      publish second.steps afterFirst = some forward →
        publish first.steps afterSecond = some reverse → forward = reverse

theorem Proposal.Compatible.symm {first second : Proposal Location Value Answer}
    (compatible : first.Compatible second) : second.Compatible first where
  preserves := compatible.preserved
  preserved := compatible.preserves
  joins _ _ _ _ _ secondPublished firstPublished reverse forward :=
    (compatible.joins firstPublished secondPublished forward reverse).symm

/-- A proposal that has an outcome from a state publishes on it. -/
theorem Proposal.publish_isSome_of_outcome? {proposal : Proposal Location Value Answer}
    {state : Location → Value} {outcome : Answer × Proposal Location Value Answer}
    (explored : proposal.outcome? state = some outcome) :
    ∃ view, publish proposal.steps state = some view := by
  obtain ⟨view, published, -⟩ := Proposal.outcome?_eq_some_iff.mp explored
  exact ⟨view, published⟩

/-- **Independence by read and write sets is a test for compatibility.** -/
theorem Proposal.Independent.compatible {first second : Proposal Location Value Answer}
    (independent : first.Independent second) : first.Compatible second where
  preserves _ _ _ published explored :=
    (second.outcome?_congr (Proposal.readsKept_of_independent independent published)) ▸ explored
  preserved _ _ _ published explored :=
    (first.outcome?_congr (Proposal.readsKept_of_independent independent.symm published)) ▸
      explored
  joins state _ _ _ _ firstPublished secondPublished forward reverse := by
    have same := publish_comm_of_independent independent.steps state
    rw [firstPublished, secondPublished, Option.bind_some, Option.bind_some, forward, reverse]
      at same
    exact Option.some.inj same

/-- **For proposals that only add, compatibility by deltas is a test for
compatibility.** -/
theorem Proposal.DeltaCompatible.compatible [AllSeparate Value]
    {first second : Proposal Location Value Answer} (firstDelta : first.IsDelta)
    (secondDelta : second.IsDelta) (compatible : first.DeltaCompatible second) :
    first.Compatible second where
  preserves _ _ _ published explored := by
    rw [firstDelta.publish_eq_add published]
    exact compatible.1.2.outcome?_add
      (fun location inside => stepsAdded_outside first.steps fun written =>
        Finset.disjoint_left.mp compatible.2.2 written inside) explored
  preserved _ _ _ published explored := by
    rw [secondDelta.publish_eq_add published]
    exact compatible.1.1.outcome?_add
      (fun location inside => stepsAdded_outside second.steps fun written =>
        Finset.disjoint_left.mp compatible.2.1 written inside) explored
  joins _ _ _ _ _ firstPublished secondPublished forward reverse := by
    rw [secondDelta.publish_eq_add forward, firstDelta.publish_eq_add reverse,
      firstDelta.publish_eq_add firstPublished, secondDelta.publish_eq_add secondPublished]
    exact AllSeparate.add_right_comm _ _ _

/-- Outcomes that a state has, whose proposals are compatible in pairs, are
published from it in order, each validated by replay when its turn comes. -/
theorem publishInOrder_of_compatible [DecidableEq Answer]
    {outcomes : List (Answer × Proposal Location Value Answer)}
    (compatible : outcomes.Pairwise fun first second => first.2.Compatible second.2)
    {world : Location → Value}
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? world = some outcome) :
    ∃ final, publishInOrder outcomes world = some final := by
  induction outcomes generalizing world with
  | nil => exact ⟨world, rfl⟩
  | cons outcome rest ih =>
      obtain ⟨headCompatible, restCompatible⟩ := List.pairwise_cons.mp compatible
      obtain ⟨view, published, same⟩ :=
        Proposal.outcome?_eq_some_iff.mp (explored outcome List.mem_cons_self)
      obtain ⟨final, restPublished⟩ :=
        ih restCompatible (world := view) fun other member =>
          (headCompatible other member).preserves published
            (explored other (List.mem_cons_of_mem outcome member))
      refine ⟨final, ?_⟩
      rw [publishInOrder, published, Option.bind_some, if_pos (congrArg Prod.fst same)]
      exact restPublished

/-- Outcomes that a state has, whose proposals are compatible in pairs, are
published to one state in every order. -/
theorem publishAll_perm_of_compatible
    {outcomes reordered : List (Answer × Proposal Location Value Answer)}
    (perm : outcomes.Perm reordered)
    (compatible : outcomes.Pairwise fun first second => first.2.Compatible second.2)
    {world : Location → Value}
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? world = some outcome) :
    publishAll (outcomes.map Prod.snd) world = publishAll (reordered.map Prod.snd) world := by
  induction perm generalizing world with
  | nil => rfl
  | @cons outcome first second _ ih =>
      obtain ⟨headCompatible, restCompatible⟩ := List.pairwise_cons.mp compatible
      obtain ⟨view, published⟩ :=
        Proposal.publish_isSome_of_outcome? (explored outcome List.mem_cons_self)
      rw [List.map_cons, List.map_cons, publishAll_cons, publishAll_cons, published,
        Option.bind_some, Option.bind_some]
      exact ih restCompatible fun other member =>
        (headCompatible other member).preserves published
          (explored other (List.mem_cons_of_mem outcome member))
  | swap first second rest =>
      obtain ⟨headCompatible, restCompatible⟩ := List.pairwise_cons.mp compatible
      have pair : second.2.Compatible first.2 := headCompatible first List.mem_cons_self
      have firstExplored := explored first (List.mem_cons_of_mem second List.mem_cons_self)
      have secondExplored := explored second List.mem_cons_self
      obtain ⟨afterFirst, firstPublished⟩ := Proposal.publish_isSome_of_outcome? firstExplored
      obtain ⟨afterSecond, secondPublished⟩ := Proposal.publish_isSome_of_outcome? secondExplored
      obtain ⟨forward, forwardPublished⟩ :=
        Proposal.publish_isSome_of_outcome? (pair.preserved firstPublished secondExplored)
      obtain ⟨reverse, reversePublished⟩ :=
        Proposal.publish_isSome_of_outcome? (pair.preserves secondPublished firstExplored)
      have same : reverse = forward :=
        pair.joins secondPublished firstPublished reversePublished forwardPublished
      simp only [List.map_cons, publishAll_cons, firstPublished, secondPublished,
        forwardPublished, reversePublished, Option.bind_some, same]
  | @trans first second third firstPerm _ ihFirst ihSecond =>
      rw [ihFirst compatible explored]
      exact ihSecond
        ((firstPerm.pairwise_iff fun related => Proposal.Compatible.symm related).mp compatible)
        fun outcome member => explored outcome (firstPerm.mem_iff.mpr member)

/-- **Compatible proposals are a wave.**  Outcomes explored from one state whose
proposals are compatible in pairs are published from that state in every order,
each validated by replay when its turn comes; all orders reach one state; and
every order is the committed run of the alternatives that answered, with the
answers that were returned. -/
theorem wave_of_compatible_every_order [DecidableEq Answer]
    {outcomes order : List (Answer × Proposal Location Value Answer)}
    (compatible : outcomes.Pairwise fun first second => first.2.Compatible second.2)
    {world : Location → Value}
    (explored : ∀ outcome ∈ outcomes, outcome.2.outcome? world = some outcome)
    (perm : outcomes.Perm order) :
    ∃ final, publishInOrder outcomes world = some final ∧
      publishInOrder order world = some final ∧
      (Region.alternatives (order.map fun outcome => outcome.2.region)).committed world =
        (order.map Prod.fst, final) := by
  obtain ⟨final, published⟩ := publishInOrder_of_compatible compatible explored
  obtain ⟨reorderedFinal, reorderedPublished⟩ :=
    publishInOrder_of_compatible
      ((perm.pairwise_iff fun related => Proposal.Compatible.symm related).mp compatible)
      fun outcome member => explored outcome (perm.mem_iff.mpr member)
  have same : final = reorderedFinal :=
    Option.some.inj ((publishAll_of_publishInOrder published).symm.trans
      ((publishAll_perm_of_compatible perm compatible explored).trans
        (publishAll_of_publishInOrder reorderedPublished)))
  refine ⟨final, published, same ▸ reorderedPublished, ?_⟩
  rw [same]
  exact publishInOrder_serializable reorderedPublished

end Compatibility

/-! ## Controls -/

namespace CompatibilityControls

open AddOnly (Kind noKinds)
open KindControls (oneA)
open DeltaControls (addB removeA)

/-- An addition of a `b` is a proposal by deltas. -/
theorem addB_isDelta : addB.IsDelta := by
  intro step member
  rw [List.mem_singleton.mp member]
  exact addKind_isAddition _

/-- Two additions of a `b` are compatible by deltas: neither has a guard, and
neither answer reads. -/
theorem addB_deltaCompatible : addB.DeltaCompatible addB := by
  refine ⟨⟨?_, ?_⟩, by decide, by decide⟩ <;>
  · intro step member state _
    rw [List.mem_singleton.mp member]
    trivial

/-- **The two tests, mixed in one wave.**  A removal of the `a` and two additions
of a `b`, explored from the state with one `a`.

* The removal is independent of an addition by read and write sets, and the two
  additions are not independent of each other by sets.
* The two additions are compatible by deltas, and the removal is no proposal by
  deltas.
* In pairs the three are compatible, so every order is published; three of the
  orders, as instances: one `b` twice and no `a`. -/
theorem mixed_wave :
    removeA.Independent addB ∧ ¬ addB.Independent addB ∧ addB.DeltaCompatible addB ∧
      ¬ removeA.IsDelta ∧
      ([((), removeA), ((), addB), ((), addB)] : List (Unit × Proposal Kind ℕ Unit)).Pairwise
        (fun first second => first.2.Compatible second.2) ∧
      (publishInOrder [((), removeA), ((), addB), ((), addB)] oneA).map
        (fun world => (world .a, world .b)) = some (0, 2) ∧
      (publishInOrder [((), addB), ((), removeA), ((), addB)] oneA).map
        (fun world => (world .a, world .b)) = some (0, 2) ∧
      (publishInOrder [((), addB), ((), addB), ((), removeA)] oneA).map
        (fun world => (world .a, world .b)) = some (0, 2) := by
  have bySets : removeA.Independent addB := by decide
  have byDeltas : addB.Compatible addB :=
    addB_deltaCompatible.compatible addB_isDelta addB_isDelta
  refine ⟨bySets, by decide, addB_deltaCompatible,
    fun delta => removeKind_not_isAddition Kind.a (delta _ List.mem_cons_self), ?_, by decide,
    by decide, by decide⟩
  refine List.pairwise_cons.mpr ⟨fun other member => ?_, List.pairwise_cons.mpr
    ⟨fun other member => ?_,
      List.pairwise_cons.mpr ⟨fun _ member => (nomatch member), List.Pairwise.nil⟩⟩⟩
  · rcases List.mem_cons.mp member with rfl | later
    · exact bySets.compatible
    · rw [List.mem_singleton.mp later]
      exact bySets.compatible
  · rw [List.mem_singleton.mp member]
    exact byDeltas

/-- **Negative, compatible**: two takers of one `a`.  After either has published,
the other has lost the outcome it had. -/
theorem not_compatible : ¬ removeA.Compatible removeA := by
  intro compatible
  have firstPublished : publish removeA.steps oneA = some noKinds := by
    show ((removeKind Kind.a).fire oneA).bind (publish []) = some noKinds
    rw [(fire_removeKind_eq_some_iff Kind.a oneA noKinds).mpr (by
      funext kind
      cases kind <;> rfl)]
    rfl
  have explored : removeA.outcome? oneA = some ((), removeA) := by
    show (publish removeA.steps oneA).map _ = _
    rw [firstPublished]
    rfl
  have still := compatible.preserves firstPublished explored
  have refused : (removeA.outcome? noKinds).isSome = false := by decide
  rw [still] at refused
  cases refused

/-- **Positive, outcomes preserved**: an addition preserves the outcome of the
read of a presence.  **Negative**: a removal of the kind does not. -/
theorem preservesOutcomes_instances :
    addB.PreservesOutcomes (⟨[seeKind Kind.b], Readout.const ()⟩ : Proposal Kind ℕ Unit) ∧
      ¬ removeA.PreservesOutcomes
        (⟨[seeKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit) := by
  constructor
  · intro state afterFirst outcome published explored
    rw [addB_isDelta.publish_eq_add published]
    exact (oneAnswer_monotone Kind.b ()).positive.outcome?_add explored _
  · intro preserves
    have firstPublished : publish removeA.steps oneA = some noKinds := by
      show ((removeKind Kind.a).fire oneA).bind (publish []) = some noKinds
      rw [(fire_removeKind_eq_some_iff Kind.a oneA noKinds).mpr (by
        funext kind
        cases kind <;> rfl)]
      rfl
    have explored : (⟨[seeKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).outcome? oneA =
        some ((), ⟨[seeKind Kind.a], Readout.const ()⟩) := by
      show (publish [seeKind Kind.a] oneA).map _ = _
      rw [publish_seeKind, if_pos (by decide)]
      rfl
    have still := preserves firstPublished explored
    have refused : ((⟨[seeKind Kind.a], Readout.const ()⟩ : Proposal Kind ℕ Unit).outcome?
        noKinds).isSome = false := by decide
    rw [still] at refused
    cases refused

end CompatibilityControls

#print axioms Proposal.Independent.compatible
#print axioms Proposal.DeltaCompatible.compatible
#print axioms publishInOrder_of_compatible
#print axioms publishAll_perm_of_compatible
#print axioms wave_of_compatible_every_order
#print axioms CompatibilityControls.addB_deltaCompatible
#print axioms CompatibilityControls.mixed_wave
#print axioms CompatibilityControls.not_compatible
#print axioms CompatibilityControls.preservesOutcomes_instances

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
