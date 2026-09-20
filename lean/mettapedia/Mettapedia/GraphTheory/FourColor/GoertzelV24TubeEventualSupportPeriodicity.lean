import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeFourRingNonidentity

/-!
# Eventual support periodicity of the physical normalized tube

The complete recurrent tube transfer has no one-ring self-loop, and a
four-ring return is not an identity relation.  Nevertheless its *reachable
support* saturates: after nine physical rings, every recurrent target in the
opposite frontier phase is reachable.  This is a Boolean-semiring transfer
fact about all paths, not an existential choice of one path.

The finite calculation below is made against the two exhaustive physical
ring choices from `GoertzelV24TubeSeedMultiplicity`; the following semantic
lemmas identify its recursively computed support with the literal
`ExactRelationalTransfer TubeRingStep`.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeEventualSupportPeriodicity

open GoertzelV24TubeRingTransfer
open GoertzelV24CorridorPumping
open GoertzelV24TubeRingSelfLoopCounterexample

/-- All physical one-ring successors of one recurrent profile, in its
exhaustively checked two-choice subsystem. -/
def recurrentNextSet (source : RecurrentTubeProfile) :
    Finset RecurrentTubeProfile :=
  {firstFullyRoutedTarget source, secondFullyRoutedTarget source}

/-- Dynamic-programming support after exactly `rings` physical extensions. -/
def recurrentReachSet : Nat → RecurrentTubeProfile → Finset RecurrentTubeProfile
  | 0, source => {source}
  | rings + 1, source =>
      (recurrentReachSet rings source).biUnion recurrentNextSet

/-- The two stored targets are exactly the successors in the full physical
ring relation, not a selected deterministic subrelation. -/
theorem mem_recurrentNextSet_iff
    (source target : RecurrentTubeProfile) :
    target ∈ recurrentNextSet source ↔
      RecurrentTubeRingStep source target := by
  simp only [recurrentNextSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨firstFullyRoutedChoice source,
        firstFullyRoutedChoice_isSuccessor source⟩
    · exact ⟨secondFullyRoutedChoice source,
        secondFullyRoutedChoice_isSuccessor source⟩
  · exact recurrentStep_target_eq_first_or_second source target

private theorem transfer_snoc_iff
    {Profile : Type*} {oneStep : Profile → Profile → Prop}
    {rings : Nat} {source target : Profile} :
    ExactRelationalTransfer oneStep (rings + 1) source target ↔
      ∃ middle, ExactRelationalTransfer oneStep rings source middle ∧
        oneStep middle target := by
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

/-- The computed support is definitionally tied to genuine physical
exact-length transfer by the exhaustive one-ring classification. -/
theorem mem_recurrentReachSet_iff :
    ∀ (rings : Nat) (source target : RecurrentTubeProfile),
      target ∈ recurrentReachSet rings source ↔
        ExactRelationalTransfer RecurrentTubeRingStep rings source target := by
  intro rings
  induction rings with
  | zero =>
      intro source target
      simp only [recurrentReachSet, Finset.mem_singleton]
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
      simp only [recurrentReachSet, Finset.mem_biUnion]
      constructor
      · rintro ⟨middle, hprefix, hnext⟩
        exact ⟨middle, (ih source middle).1 hprefix,
          (mem_recurrentNextSet_iff middle target).1 hnext⟩
      · rintro ⟨middle, hprefix, hnext⟩
        exact ⟨middle, (ih source middle).2 hprefix,
          (mem_recurrentNextSet_iff middle target).2 hnext⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The nine-ring Boolean transfer saturates every state of the opposite
phase, uniformly over all twenty physically recurrent starts. -/
theorem recurrentReachSet_nine_saturated :
    ∀ source : RecurrentTubeProfile,
      recurrentReachSet 9 source =
        Finset.univ.filter (fun target => target.1 = ! source.1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- At the first saturated stage, two more physical rings leave the entire
reachable support unchanged. -/
theorem recurrentReachSet_eleven_eq_nine :
    ∀ source : RecurrentTubeProfile,
      recurrentReachSet 11 source = recurrentReachSet 9 source := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The threshold cannot be lowered from nine to eight: the eight-ring
support lacks a target gained by the tenth ring, for every recurrent start. -/
theorem recurrentReachSet_eight_ne_ten :
    ∀ source : RecurrentTubeProfile,
      recurrentReachSet 8 source ≠ recurrentReachSet 10 source := by
  decide +kernel

/-- The support equality is not just a finite coincidence at lengths nine
and eleven: the same one-ring transfer is applied at every later step, so
the two-period equation propagates indefinitely. -/
theorem recurrentReachSet_period_two_after_nine
    (extra : Nat) (source : RecurrentTubeProfile) :
    recurrentReachSet (9 + extra + 2) source =
      recurrentReachSet (9 + extra) source := by
  induction extra with
  | zero => simpa using recurrentReachSet_eleven_eq_nine source
  | succ extra ih =>
      have hleft : 9 + (extra + 1) + 2 = (9 + extra + 2) + 1 := by omega
      have hright : 9 + (extra + 1) = (9 + extra) + 1 := by omega
      rw [hleft, hright]
      change (recurrentReachSet (9 + extra + 2) source).biUnion recurrentNextSet =
        (recurrentReachSet (9 + extra) source).biUnion recurrentNextSet
      exact congrArg (fun support => support.biUnion recurrentNextSet) ih

/-- Exact physical transfer acceptance on the recurrent subsystem depends
only on length parity once nine rings have been traversed. This is the
correct Boolean-support analogue of the source's false self-loop claim. -/
theorem recurrentTransfer_period_two_after_nine
    (extra : Nat) (source target : RecurrentTubeProfile) :
    ExactRelationalTransfer RecurrentTubeRingStep (9 + extra + 2)
        source target ↔
      ExactRelationalTransfer RecurrentTubeRingStep (9 + extra)
        source target := by
  rw [← mem_recurrentReachSet_iff (9 + extra + 2) source target,
    ← mem_recurrentReachSet_iff (9 + extra) source target,
    recurrentReachSet_period_two_after_nine extra source]

/-- Every unrestricted physical path from a recurrent frontier has a
recurrent presentation throughout. This uses closure under *all* locally
Tait-valid ring choices, not just the two displayed successor names. -/
theorem rawTransfer_closed_recurrent :
    ∀ (rings : Nat) (source : RecurrentTubeProfile)
      (target : TubeFrontierState),
      ExactRelationalTransfer TubeRingStep rings
        (recurrentProfileState source) target →
      ∃ next : RecurrentTubeProfile,
        target = recurrentProfileState next ∧
          ExactRelationalTransfer RecurrentTubeRingStep rings source next := by
  intro rings
  induction rings with
  | zero =>
      intro source target htransfer
      cases htransfer
      exact ⟨source, rfl, .zero source⟩
  | succ rings ih =>
      intro source target htransfer
      cases htransfer with
      | succ hstep htail =>
          obtain ⟨middle, hmiddle⟩ :=
            recurrent_successor_closed source _ hstep
          rw [hmiddle] at htail
          obtain ⟨next, htarget, hrest⟩ := ih middle target htail
          refine ⟨next, htarget, .succ ?_ hrest⟩
          change TubeRingStep (recurrentProfileState source)
            (recurrentProfileState middle)
          rw [← hmiddle]
          exact hstep

/-- The recurrent presentation is exact for unrestricted physical paths
between its frontier states. -/
theorem rawTransfer_iff_recurrentTransfer
    (rings : Nat) (source target : RecurrentTubeProfile) :
    ExactRelationalTransfer TubeRingStep rings
        (recurrentProfileState source) (recurrentProfileState target) ↔
      ExactRelationalTransfer RecurrentTubeRingStep rings source target := by
  constructor
  · intro hraw
    obtain ⟨next, htarget, hrestricted⟩ :=
      rawTransfer_closed_recurrent rings source _ hraw
    have hnext : next = target := recurrentProfileState_injective htarget.symm
    subst next
    exact hrestricted
  · intro hrestricted
    induction hrestricted with
    | zero => exact .zero _
    | succ hstep hrest ih => exact .succ hstep ih

/-- Once nine rings have been traversed, inserting or deleting two rings
preserves exact reachability of *every* physical complete frontier. -/
theorem rawTransfer_period_two_after_nine
    (extra : Nat) (source : RecurrentTubeProfile)
    (target : TubeFrontierState) :
    ExactRelationalTransfer TubeRingStep (9 + extra + 2)
        (recurrentProfileState source) target ↔
      ExactRelationalTransfer TubeRingStep (9 + extra)
        (recurrentProfileState source) target := by
  constructor
  · intro hlong
    obtain ⟨next, htarget, hrestricted⟩ :=
      rawTransfer_closed_recurrent _ source target hlong
    subst target
    exact (rawTransfer_iff_recurrentTransfer _ source next).2
      ((recurrentTransfer_period_two_after_nine extra source next).1 hrestricted)
  · intro hshort
    obtain ⟨next, htarget, hrestricted⟩ :=
      rawTransfer_closed_recurrent _ source target hshort
    subst target
    exact (rawTransfer_iff_recurrentTransfer _ source next).2
      ((recurrentTransfer_period_two_after_nine extra source next).2 hrestricted)

/-- An arbitrary test on the complete endpoint state sees the same Boolean
acceptance after nine-plus-two rings as after nine rings. This is a genuine
context-independent support law for the normalized physical tube. -/
theorem rawCapAcceptance_period_two_after_nine
    (extra : Nat) (source : RecurrentTubeProfile)
    (accepts : TubeFrontierState → Prop) :
    (∃ target, ExactRelationalTransfer TubeRingStep (9 + extra + 2)
        (recurrentProfileState source) target ∧ accepts target) ↔
      (∃ target, ExactRelationalTransfer TubeRingStep (9 + extra)
        (recurrentProfileState source) target ∧ accepts target) := by
  constructor
  · rintro ⟨target, htransfer, haccept⟩
    exact ⟨target, (rawTransfer_period_two_after_nine extra source target).1
      htransfer, haccept⟩
  · rintro ⟨target, htransfer, haccept⟩
    exact ⟨target, (rawTransfer_period_two_after_nine extra source target).2
      htransfer, haccept⟩

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeEventualSupportPeriodicity
