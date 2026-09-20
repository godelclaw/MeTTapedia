import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCorridorShortening

/-!
# Colour-only transfer of the literal five-port tube ring

The four named alternating strands are an extra condition on the normalized
transfer, not part of proper Tait colouring.  Here the same twenty-edge ring
is transferred using only its five input colours and the locally proper
five-bit choice.  Every such choice is retained, including the explicitly
proved non-routed choice in `GoertzelV24TubeCorridorShortening`.

This deliberately tests whether the Boolean shortening survives without the
routing restriction.  Even a positive result here concerns an open corridor;
physical insertion into an arbitrary planar map remains a separate theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeColourOnlyPeriodicity

open GoertzelV24TubeRingTransfer
open GoertzelV24CorridorPumping
open GoertzelV24WindingClassification

abbrev ColourWord := Fin 5 → StrandColor

/-- Terminal labels are ignored by `Valid` and `newColor`; this fixed dummy
array merely lets the existing physical colour equations be reused. -/
def dummyState (word : ColourWord) : TubeFrontierState :=
  ⟨word, fun i => i.castSucc⟩

/-- One locally proper tube ring, with no four-strand routing restriction. -/
def ColourStep (source target : ColourWord) : Prop :=
  ∃ choice : TubeRingChoice,
    choice.Valid (dummyState source) ∧
      target = newColor (dummyState source) choice

/-- The executable validity test is *exactly* local Tait properness of the
same twenty-edge ring, not a hidden routing predicate. -/
theorem valid_iff_locallyTait (source : ColourWord)
    (choice : TubeRingChoice) :
    choice.Valid (dummyState source) ↔
      choice.LocallyTait (dummyState source) := by
  constructor
  · exact choice.locallyTait_of_valid _
  · intro hlocal vertex
    exact (hlocal.2 vertex).1

/-- Executable full successor set for colour words. -/
def nextSet (source : ColourWord) : Finset ColourWord :=
  (Finset.univ.filter (fun choice : TubeRingChoice =>
      decide (choice.Valid (dummyState source)))).image
    (newColor (dummyState source))

theorem mem_nextSet_iff (source target : ColourWord) :
    target ∈ nextSet source ↔ ColourStep source target := by
  simp only [nextSet, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, decide_eq_true_eq]
  exact exists_congr (fun choice => and_congr_right fun _ => eq_comm)

/-- Endpoints after exactly `rings` unconstrained, locally proper rings. -/
def reachSet : Nat → ColourWord → Finset ColourWord
  | 0, source => {source}
  | rings + 1, source => (reachSet rings source).biUnion nextSet

private theorem transfer_snoc_iff
    {rings : Nat} {source target : ColourWord} :
    ExactRelationalTransfer ColourStep (rings + 1) source target ↔
      ∃ middle, ExactRelationalTransfer ColourStep rings source middle ∧
        ColourStep middle target := by
  constructor
  · intro htransfer
    induction rings generalizing source with
    | zero =>
        cases htransfer with
        | succ hstep htail =>
            cases htail
            exact ⟨source, .zero source, hstep⟩
    | succ rings ih =>
        cases htransfer with
        | succ hstep htail =>
            obtain ⟨middle, hprefix, hlast⟩ := ih htail
            exact ⟨middle, .succ hstep hprefix, hlast⟩
  · rintro ⟨middle, hprefix, hlast⟩
    exact hprefix.comp (.succ hlast (.zero target))

theorem mem_reachSet_iff :
    ∀ (rings : Nat) (source target : ColourWord),
      target ∈ reachSet rings source ↔
        ExactRelationalTransfer ColourStep rings source target := by
  intro rings
  induction rings with
  | zero =>
      intro source target
      simp only [reachSet, Finset.mem_singleton]
      constructor
      · intro h
        subst target
        exact .zero source
      · intro h
        cases h
        rfl
  | succ rings ih =>
      intro source target
      rw [transfer_snoc_iff]
      simp only [reachSet, Finset.mem_biUnion]
      constructor
      · rintro ⟨middle, hprefix, hnext⟩
        exact ⟨middle, (ih source middle).1 hprefix,
          (mem_nextSet_iff middle target).1 hnext⟩
      · rintro ⟨middle, hprefix, hnext⟩
        exact ⟨middle, (ih source middle).2 hprefix,
          (mem_nextSet_iff middle target).2 hnext⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The colour word on the previously normalized recurrent tube seed. -/
def seedWord : ColourWord :=
  (recurrentProfileState (true, (5 : Fin 10))).color

/-- The non-routed but proper branch from the companion obstruction file
is included in this unrestricted colour transfer. -/
theorem escapingChoice_isColourStep :
    ColourStep seedWord
      (newColor (dummyState seedWord)
        GoertzelV24TubeCorridorShortening.escapingChoice) := by
  refine ⟨GoertzelV24TubeCorridorShortening.escapingChoice, ?_, rfl⟩
  decide +kernel

/-- All locally proper branches, including the non-routed one, have the
same possible colour-word endpoints after four and six rings from the
physical seed. This is a finite check of one *actual* source word, not a
claim about every possible external context. -/
theorem reachSet_six_eq_four_seed :
    reachSet 6 seedWord = reachSet 4 seedWord := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Forgetting strand routing strengthens the return: the whole colour
support is stationary after four rings, not merely two-periodic. -/
theorem reachSet_five_eq_four_seed :
    reachSet 5 seedWord = reachSet 4 seedWord := by
  decide +kernel

theorem reachSet_stable_after_four (extra : Nat) :
    reachSet (4 + extra + 1) seedWord = reachSet (4 + extra) seedWord := by
  induction extra with
  | zero => simpa using reachSet_five_eq_four_seed
  | succ extra ih =>
      have hleft : 4 + (extra + 1) + 1 = (4 + extra + 1) + 1 := by omega
      have hright : 4 + (extra + 1) = (4 + extra) + 1 := by omega
      rw [hleft, hright]
      change (reachSet (4 + extra + 1) seedWord).biUnion nextSet =
        (reachSet (4 + extra) seedWord).biUnion nextSet
      exact congrArg (fun support => support.biUnion nextSet) ih

theorem reachSet_period_two_after_four
    (extra : Nat) :
    reachSet (4 + extra + 2) seedWord = reachSet (4 + extra) seedWord := by
  induction extra with
  | zero => simpa using reachSet_six_eq_four_seed
  | succ extra ih =>
      have hleft : 4 + (extra + 1) + 2 = (4 + extra + 2) + 1 := by omega
      have hright : 4 + (extra + 1) = (4 + extra) + 1 := by omega
      rw [hleft, hright]
      change (reachSet (4 + extra + 2) seedWord).biUnion nextSet =
        (reachSet (4 + extra) seedWord).biUnion nextSet
      exact congrArg (fun support => support.biUnion nextSet) ih

/-- From the seed, the all-colouring quotient, not merely the four-strand
routed quotient, has a cap-independent two-ring Boolean return. -/
theorem capAcceptance_period_two_after_four
    (extra : Nat) (accepts : ColourWord → Prop) :
    (∃ target, ExactRelationalTransfer ColourStep (4 + extra + 2)
      seedWord target ∧ accepts target) ↔
      (∃ target, ExactRelationalTransfer ColourStep (4 + extra)
        seedWord target ∧ accepts target) := by
  have hpoint (target : ColourWord) :
      ExactRelationalTransfer ColourStep (4 + extra + 2) seedWord target ↔
        ExactRelationalTransfer ColourStep (4 + extra) seedWord target := by
    rw [← mem_reachSet_iff, ← mem_reachSet_iff,
      reachSet_period_two_after_four extra]
  constructor
  · rintro ⟨target, htransfer, haccept⟩
    exact ⟨target, (hpoint target).1 htransfer, haccept⟩
  · rintro ⟨target, htransfer, haccept⟩
    exact ⟨target, (hpoint target).2 htransfer, haccept⟩

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeColourOnlyPeriodicity
