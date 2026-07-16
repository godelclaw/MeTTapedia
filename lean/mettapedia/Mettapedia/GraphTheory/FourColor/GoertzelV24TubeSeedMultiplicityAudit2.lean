import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityDefs

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA4_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 4) ↔
        choice = phaseAFirstFullyRoutedChoice 4 ∨
        choice = phaseASecondFullyRoutedChoice 4 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA5_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 5) ↔
        choice = phaseAFirstFullyRoutedChoice 5 ∨
        choice = phaseASecondFullyRoutedChoice 5 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB4_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 4) ↔
        choice = phaseBFirstFullyRoutedChoice 4 ∨
        choice = phaseBSecondFullyRoutedChoice 4 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB5_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 5) ↔
        choice = phaseBFirstFullyRoutedChoice 5 ∨
        choice = phaseBSecondFullyRoutedChoice 5 := by decide

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
