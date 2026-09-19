import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicity

/-!
# A physical recurrent tube profile without a one-ring self-loop

The source playbook's L2 asks every alive corridor profile to extend through
one hexagonal ring back to itself. Its proposed weak fallback infers access
to such a loop from recurrence. The normalized `(5,0)` tube already separates
those statements: the reflected good cap state supports a genuine locally
Tait-coloured four-ring return, but no genuine one-ring self-return.

The previously checked two-choice classification is exhaustive on each of
the twenty recurrent profiles. Consequently *every* tube-ring successor of
the good seed remains in that recurrent set, at every length. Since no state
in the set has a one-ring self-loop, the proposed weak-L2 fallback (reach a
self-loop after finitely many rings) fails for this specific normalized tube
transfer too. This does not settle an L2 restricted by a stronger
counterexample-specific relevance predicate, nor every possible quotient of
corridor profiles. Such a filter or quotient must establish its own physical
correspondence and show it preserves the data the splice needs.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingSelfLoopCounterexample

open GoertzelV24TubeRingTransfer
open GoertzelV24CorridorPumping

/-- The witness is a legal tracked frontier, not a dead or malformed state. -/
theorem seed_valid : normalizedTubeSeed.Valid := by
  decide +kernel

/-- No choice of the five split decisions realizes an exact one-ring return
with the same colours and the same four tracked-terminal identities. -/
theorem seed_no_oneRingReturn :
    ¬ TubeRingStep normalizedTubeSeed normalizedTubeSeed := by
  decide +kernel

/-- The same obstruction holds at every one of the twenty explicitly
recurrent normalized tube profiles. This checks the *full* one-ring relation
at each state, not merely the selected alternating successor relation. -/
theorem recurrentProfile_no_oneRingSelfLoop
    (profile : RecurrentTubeProfile) :
    ¬ RecurrentTubeRingStep profile profile := by
  obtain ⟨phase, index⟩ := profile
  cases phase <;> fin_cases index <;>
    dsimp [RecurrentTubeRingStep, recurrentProfileState] <;> decide +kernel

/-- The new frontier is determined by one locally valid ring choice: its
colours are computed by the ring, and its terminal locations by the actual
tracked-component reachability. -/
private theorem successor_target_unique
    {source first second : TubeFrontierState} {choice : TubeRingChoice}
    (hfirst : IsTubeRingSuccessor source first choice)
    (hsecond : IsTubeRingSuccessor source second choice) :
    first = second := by
  cases first with
  | mk firstColor firstTerminal =>
    cases second with
    | mk secondColor secondTerminal =>
      congr 1
      · funext position
        exact (hfirst.2.2.2.1 position).trans
          (hsecond.2.2.2.1 position).symm
      · exact (computedRoutedTerminal_eq_of_successor hfirst).symm.trans
          (computedRoutedTerminal_eq_of_successor hsecond)

/-- The twenty recurrent state records are distinct; the phase bit cannot
be erased by equality of their complete colour-and-routing data. -/
theorem recurrentProfileState_injective :
    Function.Injective recurrentProfileState := by
  decide +kernel

/-- Every genuine ring move between recurrent profiles is one of the two
audited targets. This relates the finite target table to the full physical
relation, rather than merely certifying two selected moves. -/
theorem recurrentStep_target_eq_first_or_second
    (source target : RecurrentTubeProfile)
    (hstep : RecurrentTubeRingStep source target) :
    target = firstFullyRoutedTarget source ∨
      target = secondFullyRoutedTarget source := by
  change TubeRingStep (recurrentProfileState source)
    (recurrentProfileState target) at hstep
  obtain ⟨choice, hchoice⟩ := hstep
  have hfully : choice.FullyRouted (recurrentProfileState source) := by
    change IsFullyRoutedTubeRingChoice (recurrentProfileState source) choice
      (computedRoutedTerminal (recurrentProfileState source) choice)
    rw [computedRoutedTerminal_eq_of_successor hchoice]
    exact isFullyRoutedTubeRingChoice_of_successor hchoice
  rcases (recurrentProfile_fullyRoutedChoice_iff source choice).mp hfully with
    hfirst | hsecond
  · subst choice
    exact Or.inl (recurrentProfileState_injective
      (successor_target_unique hchoice
        (firstFullyRoutedChoice_isSuccessor source)))
  · subst choice
    exact Or.inr (recurrentProfileState_injective
      (successor_target_unique hchoice
        (secondFullyRoutedChoice_isSuccessor source)))

/-- A ring changes the complete frontier's phase on *either* locally valid
branch. Thus the source's Pascal-index "stay" is not an identity move on the
complete colour-and-routing profile. -/
theorem recurrentStep_phase_flip
    (source target : RecurrentTubeProfile)
    (hstep : RecurrentTubeRingStep source target) :
    target.1 = ! source.1 := by
  rcases recurrentStep_target_eq_first_or_second source target hstep with
    rfl | rfl
  · rcases source with ⟨phase, index⟩
    cases phase <;> rfl
  · rcases source with ⟨phase, index⟩
    cases phase <;> rfl

/-- Phase is a length-parity invariant of every physical recurrent path, not
only of the selected successor used to exhibit the four-ring return. -/
theorem recurrentTransfer_phase
    {length : Nat} {source target : RecurrentTubeProfile}
    (htransfer : ExactRelationalTransfer RecurrentTubeRingStep length source target) :
    target.1 = (Bool.not^[length]) source.1 := by
  induction htransfer with
  | zero => simp
  | @succ length source next target hstep htail ih =>
      rw [ih, recurrentStep_phase_flip source next hstep]
      simp [Function.iterate_succ_apply]

private theorem iterate_bool_not_even (bit : Bool) (cycles : Nat) :
    (Bool.not^[2 * cycles]) bit = bit := by
  induction cycles with
  | zero => simp
  | succ cycles ih =>
      calc
        (Bool.not^[2 * (cycles + 1)]) bit =
            (Bool.not^[2 + 2 * cycles]) bit := by congr 1; omega
        _ = (Bool.not^[2]) ((Bool.not^[2 * cycles]) bit) :=
          Function.iterate_add_apply Bool.not 2 (2 * cycles) bit
        _ = bit := by simp [ih]

private theorem iterate_bool_not_odd (bit : Bool) (length : Nat)
    (hodd : Odd length) :
    (Bool.not^[length]) bit = ! bit := by
  obtain ⟨cycles, rfl⟩ := hodd
  calc
    (Bool.not^[2 * cycles + 1]) bit =
        (Bool.not^[1 + 2 * cycles]) bit := by congr 1; omega
    _ = (Bool.not^[1]) ((Bool.not^[2 * cycles]) bit) :=
      Function.iterate_add_apply Bool.not 1 (2 * cycles) bit
    _ = ! bit := by simp [iterate_bool_not_even]

/-- In particular a corridor with an odd number of physical rings can
never return to its complete recurrent profile, even when arbitrary valid
split choices are allowed at every ring. -/
theorem recurrent_oddLength_no_return
    (length : Nat) (hodd : Odd length) (source : RecurrentTubeProfile) :
    ¬ ExactRelationalTransfer RecurrentTubeRingStep length source source := by
  intro hreturn
  have hphase := recurrentTransfer_phase hreturn
  rw [iterate_bool_not_odd source.1 length hodd] at hphase
  cases hbit : source.1 <;> simp [hbit] at hphase

/-- The exhaustive two-choice certificate is closure under the *full*
physical tube-ring relation, not only its named selected successors. -/
theorem recurrent_successor_closed
    (source : RecurrentTubeProfile) (target : TubeFrontierState)
    (hstep : TubeRingStep (recurrentProfileState source) target) :
    ∃ next : RecurrentTubeProfile,
      target = recurrentProfileState next := by
  obtain ⟨choice, hchoice⟩ := hstep
  have hfully : choice.FullyRouted (recurrentProfileState source) := by
    change IsFullyRoutedTubeRingChoice (recurrentProfileState source) choice
      (computedRoutedTerminal (recurrentProfileState source) choice)
    rw [computedRoutedTerminal_eq_of_successor hchoice]
    exact isFullyRoutedTubeRingChoice_of_successor hchoice
  obtain ⟨next, hnext⟩ :=
    recurrentProfile_fullyRouted_closed source choice hfully
  exact ⟨next, successor_target_unique hchoice hnext⟩

/-- Every exact-length physical corridor stays in the checked twenty-state
set, and its final phase records the parity of the complete path. -/
theorem recurrent_exactTransfer_phase_closed :
    ∀ (length : Nat) (source : RecurrentTubeProfile)
      (target : TubeFrontierState),
      ExactRelationalTransfer TubeRingStep length
        (recurrentProfileState source) target →
      ∃ next : RecurrentTubeProfile,
        target = recurrentProfileState next ∧
        next.1 = (Bool.not^[length]) source.1 := by
  intro length
  induction length with
  | zero =>
      intro source target htransfer
      cases htransfer
      exact ⟨source, rfl, by simp⟩
  | succ length ih =>
      intro source target htransfer
      cases htransfer with
      | succ hstep htail =>
          obtain ⟨middle, hmiddle⟩ :=
            recurrent_successor_closed source _ hstep
          rw [hmiddle] at htail
          obtain ⟨next, htarget, hphase⟩ := ih middle target htail
          refine ⟨next, htarget, ?_⟩
          rw [hphase]
          have hflip : middle.1 = ! source.1 := by
            apply recurrentStep_phase_flip source middle
            change TubeRingStep (recurrentProfileState source)
              (recurrentProfileState middle)
            rw [← hmiddle]
            exact hstep
          rw [hflip]
          simp [Function.iterate_succ_apply]

/-- The phase certificate entails the earlier full-relation closure fact. -/
theorem recurrent_exactTransfer_closed
    (length : Nat) (source : RecurrentTubeProfile)
    (target : TubeFrontierState)
    (htransfer : ExactRelationalTransfer TubeRingStep length
      (recurrentProfileState source) target) :
    ∃ next : RecurrentTubeProfile,
      target = recurrentProfileState next := by
  obtain ⟨next, htarget, _⟩ :=
    recurrent_exactTransfer_phase_closed length source target htransfer
  exact ⟨next, htarget⟩

/-- Odd-length return is impossible for the unrestricted *physical* ring
relation too: the exhaustive closure certificate ensures that no hidden
successor leaves the phase-graded twenty-state subsystem. -/
theorem recurrent_rawOddLength_no_return
    (length : Nat) (hodd : Odd length) (source : RecurrentTubeProfile) :
    ¬ ExactRelationalTransfer TubeRingStep length
      (recurrentProfileState source) (recurrentProfileState source) := by
  intro hreturn
  obtain ⟨next, htarget, hphase⟩ :=
    recurrent_exactTransfer_phase_closed length source _ hreturn
  have hnext : next = source :=
    recurrentProfileState_injective htarget.symm
  subst next
  rw [iterate_bool_not_odd source.1 length hodd] at hphase
  cases hbit : source.1 <;> simp [hbit] at hphase

/-- The reflected good cap state has no odd-length return in the full
ring relation. Its certified four-ring return is therefore genuinely
periodic, not a disguised one-ring padding argument. -/
theorem normalizedTubeSeed_oddLength_no_return
    (length : Nat) (hodd : Odd length) :
    ¬ ExactRelationalTransfer TubeRingStep length
      normalizedTubeSeed normalizedTubeSeed := by
  change ¬ ExactRelationalTransfer TubeRingStep length
    (recurrentProfileState (true, (5 : Fin 10)))
    (recurrentProfileState (true, (5 : Fin 10)))
  exact recurrent_rawOddLength_no_return length hodd _

private theorem normalizedTubeSeed_no_twoRingReturn_recurrent :
    ¬ ∃ middle : RecurrentTubeProfile,
      RecurrentTubeRingStep (true, (5 : Fin 10)) middle ∧
      RecurrentTubeRingStep middle (true, (5 : Fin 10)) := by
  rintro ⟨middle, hfirst, hsecond⟩
  rcases recurrentStep_target_eq_first_or_second _ middle hfirst with
    rfl | rfl
  all_goals
    rcases recurrentStep_target_eq_first_or_second _ _ hsecond with
      htarget | htarget
  all_goals simp [firstFullyRoutedTarget, secondFullyRoutedTarget,
    phaseAFirstFullyRoutedTarget, phaseASecondFullyRoutedTarget,
    phaseBFirstFullyRoutedTarget, phaseBSecondFullyRoutedTarget] at htarget

/-- The four-ring return is the *shortest positive return* of the reflected
good cap state in this complete physical transfer: lengths one and three
are ruled out by phase, and length two by the exhaustive two-choice table. -/
theorem normalizedTubeSeed_no_twoRingReturn :
    ¬ ExactRelationalTransfer TubeRingStep 2
      normalizedTubeSeed normalizedTubeSeed := by
  intro hreturn
  cases hreturn with
  | succ hfirst htail =>
      cases htail with
      | succ hsecond hzero =>
          cases hzero
          obtain ⟨middle, hmiddle⟩ :=
            recurrent_successor_closed (true, (5 : Fin 10)) _ hfirst
          rw [hmiddle] at hfirst hsecond
          exact normalizedTubeSeed_no_twoRingReturn_recurrent
            ⟨middle, hfirst, hsecond⟩

/-- Four rings is the least strictly positive return length for the physical
normalized tube seed. A zero-length identity is, of course, always possible. -/
theorem normalizedTubeSeed_shortestPositiveReturn
    (length : Nat) (hpositive : 0 < length)
    (hreturn : ExactRelationalTransfer TubeRingStep length
      normalizedTubeSeed normalizedTubeSeed) :
    4 ≤ length := by
  by_contra hshort
  have hlt : length < 4 := by omega
  interval_cases length
  · exact normalizedTubeSeed_oddLength_no_return 1 (by decide) hreturn
  · exact normalizedTubeSeed_no_twoRingReturn hreturn
  · exact normalizedTubeSeed_oddLength_no_return 3 (by decide) hreturn

/-- No finite extension from the reflected good cap state reaches any
one-ring-self-looping state. This refutes the playbook's weak-L2 fallback
for the present normalized tube transfer, without relying on a guessed
period bound. -/
theorem seed_never_reaches_oneRingSelfLoop
    (length : Nat) (target : TubeFrontierState)
    (htransfer : ExactRelationalTransfer TubeRingStep length
      normalizedTubeSeed target) :
    ¬ TubeRingStep target target := by
  have hseed : normalizedTubeSeed =
      recurrentProfileState (true, (5 : Fin 10)) := rfl
  rw [hseed] at htransfer
  obtain ⟨next, hnext⟩ :=
    recurrent_exactTransfer_closed length _ target htransfer
  rw [hnext]
  exact recurrentProfile_no_oneRingSelfLoop next

/-- In the source cap coordinates, with its proved reflection into the
normalized ring coordinates, the same one-ring obstruction holds. -/
theorem reflected_goodCap_no_oneRingReturn :
    ¬ TubeRingStep
      (goodTubeCapState.reindex goodTubeCapReflection)
      (goodTubeCapState.reindex goodTubeCapReflection) := by
  rw [goodTubeCapState_reindex_eq_normalizedTubeSeed]
  exact seed_no_oneRingReturn

/-- A live, properly colourable periodic profile need not have the L2
one-ring self-loop. The four-ring return is a genuine compositional transfer,
not merely an abstract directed cycle. -/
theorem live_recurrent_without_oneRingReturn :
    ∃ state : TubeFrontierState,
      state.Valid ∧
      ExactRelationalTransfer TubeRingStep 4 state state ∧
      (∃ coloring : TubeCorridorTaitColoring 4 state state,
        coloring.LocallyTait) ∧
      ¬ TubeRingStep state state := by
  exact ⟨normalizedTubeSeed, seed_valid,
    normalizedTubeSeed_fourRingReturn,
    normalizedTubeSeed_fourRingTaitColoring,
    seed_no_oneRingReturn⟩

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingSelfLoopCounterexample
