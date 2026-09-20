import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingSelfLoopCounterexample

/-!
# A physical four-ring return is not an identity transfer

The normalized good cap has a genuine four-ring return.  That is an
existential path through the tube relation, not an identity law for the
four-ring transfer.  The same seed has a second genuine four-ring path to a
different complete colour-and-routing frontier.  Both paths assemble to
locally Tait-proper corridor colourings.

Consequently any replacement of the source's false one-ring self-loop by a
positive-period pump still owes a context-sensitive support or matrix law.
Recurrence alone cannot discharge reverse completion.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeFourRingNonidentity

open GoertzelV24TubeRingTransfer
open GoertzelV24CorridorPumping

private theorem firstStep (source : RecurrentTubeProfile) :
    TubeRingStep (recurrentProfileState source)
      (recurrentProfileState (firstFullyRoutedTarget source)) :=
  ⟨firstFullyRoutedChoice source, firstFullyRoutedChoice_isSuccessor source⟩

/-- An alternative physical four-ring path from the good seed ends at a
different full frontier state.  Each step is one of the certified local
five-bit split choices, and terminal identities are carried through. -/
theorem normalizedTubeSeed_fourRingOffDiagonal :
    ExactRelationalTransfer TubeRingStep 4 normalizedTubeSeed
      (recurrentPhaseBState 8) := by
  have h0 : TubeRingStep normalizedTubeSeed (recurrentPhaseAState 9) := by
    simpa [normalizedTubeSeed, recurrentProfileState, firstFullyRoutedTarget,
      phaseBFirstFullyRoutedTarget] using firstStep (true, (5 : Fin 10))
  have h1 : TubeRingStep (recurrentPhaseAState 9)
      (recurrentPhaseBState 9) := by
    simpa [recurrentProfileState, firstFullyRoutedTarget,
      phaseAFirstFullyRoutedTarget] using firstStep (false, (9 : Fin 10))
  have h2 : TubeRingStep (recurrentPhaseBState 9)
      (recurrentPhaseAState 8) := by
    simpa [recurrentProfileState, firstFullyRoutedTarget,
      phaseBFirstFullyRoutedTarget] using firstStep (true, (9 : Fin 10))
  have h3 : TubeRingStep (recurrentPhaseAState 8)
      (recurrentPhaseBState 8) := by
    simpa [recurrentProfileState, firstFullyRoutedTarget,
      phaseAFirstFullyRoutedTarget] using firstStep (false, (8 : Fin 10))
  exact .succ h0 (.succ h1 (.succ h2 (.succ h3 (.zero _))))

/-- The alternative endpoint changes the actual five-port colour word. -/
theorem offDiagonalColorWord_ne_seed :
    (recurrentPhaseBState 8).color ≠ normalizedTubeSeed.color := by
  decide +kernel

/-- It changes the tracked terminal arrangement as well. -/
theorem offDiagonalTerminal_ne_seed :
    (recurrentPhaseBState 8).terminal ≠ normalizedTubeSeed.terminal := by
  decide +kernel

/-- The alternative endpoint is not the seed as a complete frontier. -/
theorem offDiagonalTarget_ne_seed :
    recurrentPhaseBState 8 ≠ normalizedTubeSeed := by
  intro h
  exact offDiagonalColorWord_ne_seed (congrArg TubeFrontierState.color h)

/-- The off-diagonal four-ring path is physically colour-realizable, not just
a path in a coarser profile graph. -/
theorem normalizedTubeSeed_fourRingOffDiagonalTaitColoring :
    ∃ coloring : TubeCorridorTaitColoring 4 normalizedTubeSeed
        (recurrentPhaseBState 8),
      coloring.LocallyTait :=
  exactTransfer_exists_locallyTaitColoring
    normalizedTubeSeed_fourRingOffDiagonal

/-- Four-ring recurrence is not the stronger identity-like statement that
every physical four-ring extension preserves the full frontier profile. -/
theorem normalizedTubeSeed_fourRing_not_identity :
    ¬ ∀ target : TubeFrontierState,
      ExactRelationalTransfer TubeRingStep 4 normalizedTubeSeed target →
        target = normalizedTubeSeed := by
  intro hall
  exact offDiagonalTarget_ne_seed
    (hall (recurrentPhaseBState 8) normalizedTubeSeed_fourRingOffDiagonal)

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeFourRingNonidentity
