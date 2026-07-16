import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityDefs

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA2_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 2) ↔
        choice = phaseAFirstFullyRoutedChoice 2 ∨
        choice = phaseASecondFullyRoutedChoice 2 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA3_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 3) ↔
        choice = phaseAFirstFullyRoutedChoice 3 ∨
        choice = phaseASecondFullyRoutedChoice 3 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB2_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 2) ↔
        choice = phaseBFirstFullyRoutedChoice 2 ∨
        choice = phaseBSecondFullyRoutedChoice 2 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB3_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 3) ↔
        choice = phaseBFirstFullyRoutedChoice 3 ∨
        choice = phaseBSecondFullyRoutedChoice 3 := by decide

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
