import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeSeedMultiplicityDefs

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA6_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 6) ↔
        choice = phaseAFirstFullyRoutedChoice 6 ∨
        choice = phaseASecondFullyRoutedChoice 6 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseA7_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseAState 7) ↔
        choice = phaseAFirstFullyRoutedChoice 7 ∨
        choice = phaseASecondFullyRoutedChoice 7 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB6_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 6) ↔
        choice = phaseBFirstFullyRoutedChoice 6 ∨
        choice = phaseBSecondFullyRoutedChoice 6 := by decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 12000000 in
theorem phaseB7_fullyRoutedChoice_iff :
    ∀ choice : TubeRingChoice,
      choice.FullyRouted (recurrentPhaseBState 7) ↔
        choice = phaseBFirstFullyRoutedChoice 7 ∨
        choice = phaseBSecondFullyRoutedChoice 7 := by decide

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
