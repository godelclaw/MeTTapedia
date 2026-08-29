import KrennComponent6.Root
import KrennComponent6.SelectedBridgeB0
import KrennComponent6.SelectedBridgeB1
import KrennComponent6.SelectedBridgeB2
import KrennComponent6.SelectedBridgeB3
import KrennComponent6.SelectedBridgeB4
import KrennComponent6.SelectedBridgeB5
import KrennComponent6.SelectedBridgeB6
import KrennComponent6.SelectedBridgeB7

namespace Krenn.Component6.SelectedSubtreeROOT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart ``. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component6.Root.RootCommonZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component6.SelectedBridgeB0.selectedLeafB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      · exact Krenn.Component6.SelectedBridgeB1.selectedLeafB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component6.SelectedBridgeB2.selectedLeafB2Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component6.SelectedBridgeB3.selectedLeafB3Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component6.SelectedBridgeB4.selectedLeafB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      · exact Krenn.Component6.SelectedBridgeB5.selectedLeafB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component6.SelectedBridgeB6.selectedLeafB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component6.SelectedBridgeB7.selectedLeafB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])

/-- The frozen carrier subtree rooted at `` has no common zero. -/
theorem subtreeROOTImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component6.Root.RootCommonZero values)
    : False := by
  exact rootImpossible values rootZero

#print axioms Krenn.Component6.SelectedSubtreeROOT.subtreeROOTImpossible

end Krenn.Component6.SelectedSubtreeROOT
