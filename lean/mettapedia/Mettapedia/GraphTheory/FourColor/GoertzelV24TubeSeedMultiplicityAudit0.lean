import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityDefs

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA0_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 0) ↔
        choice = phaseAFirstFullyRoutedChoice 0 ∨
        choice = phaseASecondFullyRoutedChoice 0 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA1_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 1) ↔
        choice = phaseAFirstFullyRoutedChoice 1 ∨
        choice = phaseASecondFullyRoutedChoice 1 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB0_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 0) ↔
        choice = phaseBFirstFullyRoutedChoice 0 ∨
        choice = phaseBSecondFullyRoutedChoice 0 := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB1_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 1) ↔
        choice = phaseBFirstFullyRoutedChoice 1 ∨
        choice = phaseBSecondFullyRoutedChoice 1 := by
  decide

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
