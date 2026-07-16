import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityDefs

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA8_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 8) ↔
        choice = phaseAFirstFullyRoutedChoice 8 ∨
        choice = phaseASecondFullyRoutedChoice 8 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA9_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 9) ↔
        choice = phaseAFirstFullyRoutedChoice 9 ∨
        choice = phaseASecondFullyRoutedChoice 9 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB8_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 8) ↔
        choice = phaseBFirstFullyRoutedChoice 8 ∨
        choice = phaseBSecondFullyRoutedChoice 8 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB9_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 9) ↔
        choice = phaseBFirstFullyRoutedChoice 9 ∨
        choice = phaseBSecondFullyRoutedChoice 9 := by decide

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
