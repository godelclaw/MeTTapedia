import KrennComponent55.Root
import KrennComponent55.SelectedBridgeB0
import KrennComponent55.SelectedBridgeB1
import KrennComponent55.SelectedBridgeB2
import KrennComponent55.SelectedBridgeB3
import KrennComponent55.SelectedBridgeB4_0
import KrennComponent55.SelectedBridgeB4_1
import KrennComponent55.SelectedBridgeB4_2_0
import KrennComponent55.SelectedBridgeB4_2_1
import KrennComponent55.SelectedBridgeB4_2_2
import KrennComponent55.SelectedBridgeB4_2_3
import KrennComponent55.SelectedBridgeB4_2_4
import KrennComponent55.SelectedBridgeB4_2_5
import KrennComponent55.SelectedBridgeB4_2_6
import KrennComponent55.SelectedBridgeB4_2_7
import KrennComponent55.SelectedBridgeB4_3
import KrennComponent55.SelectedBridgeB4_4
import KrennComponent55.SelectedBridgeB4_5
import KrennComponent55.SelectedBridgeB4_6
import KrennComponent55.SelectedBridgeB4_7
import KrennComponent55.SelectedBridgeB5
import KrennComponent55.SelectedBridgeB6_0
import KrennComponent55.SelectedBridgeB6_1
import KrennComponent55.SelectedBridgeB6_2_0
import KrennComponent55.SelectedBridgeB6_2_1
import KrennComponent55.SelectedBridgeB6_2_2
import KrennComponent55.SelectedBridgeB6_2_3
import KrennComponent55.SelectedBridgeB6_2_4
import KrennComponent55.SelectedBridgeB6_2_5
import KrennComponent55.SelectedBridgeB6_2_6
import KrennComponent55.SelectedBridgeB6_2_7
import KrennComponent55.SelectedBridgeB6_3
import KrennComponent55.SelectedBridgeB6_4
import KrennComponent55.SelectedBridgeB6_5
import KrennComponent55.SelectedBridgeB6_6
import KrennComponent55.SelectedBridgeB6_7
import KrennComponent55.SelectedBridgeB7

namespace Krenn.Component55.SelectedSubtreeROOT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b4.2`. -/
theorem nodeB42Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 52 = 0
  ·
    by_cases zeroD2C1 : values 53 = 0
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB4_2_0.selectedLeafB4_2_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB4_2_1.selectedLeafB4_2_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 54)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB4_2_2.selectedLeafB4_2_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 53)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB4_2_3.selectedLeafB4_2_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 53)⁻¹ (by simp [zeroD2C1]) (values 54)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 53 = 0
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB4_2_4.selectedLeafB4_2_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB4_2_5.selectedLeafB4_2_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 54)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB4_2_6.selectedLeafB4_2_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) (values 53)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB4_2_7.selectedLeafB4_2_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) (values 53)⁻¹ (by simp [zeroD2C1]) (values 54)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.2`. -/
theorem nodeB62Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 52 = 0
  ·
    by_cases zeroD2C1 : values 53 = 0
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB6_2_0.selectedLeafB6_2_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB6_2_1.selectedLeafB6_2_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 54)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB6_2_2.selectedLeafB6_2_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 53)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB6_2_3.selectedLeafB6_2_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 53)⁻¹ (by simp [zeroD2C1]) (values 54)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 53 = 0
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB6_2_4.selectedLeafB6_2_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB6_2_5.selectedLeafB6_2_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 54)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 54 = 0
      · exact Krenn.Component55.SelectedBridgeB6_2_6.selectedLeafB6_2_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) (values 53)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component55.SelectedBridgeB6_2_7.selectedLeafB6_2_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 52)⁻¹ (by simp [zeroD2C0]) (values 53)⁻¹ (by simp [zeroD2C1]) (values 54)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component55.SelectedBridgeB4_0.selectedLeafB4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB4_1.selectedLeafB4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB42Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB4_3.selectedLeafB4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component55.SelectedBridgeB4_4.selectedLeafB4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB4_5.selectedLeafB4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component55.SelectedBridgeB4_6.selectedLeafB4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB4_7.selectedLeafB4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b6`. -/
theorem nodeB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component55.SelectedBridgeB6_0.selectedLeafB6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB6_1.selectedLeafB6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB62Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB6_3.selectedLeafB6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component55.SelectedBridgeB6_4.selectedLeafB6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB6_5.selectedLeafB6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component55.SelectedBridgeB6_6.selectedLeafB6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component55.SelectedBridgeB6_7.selectedLeafB6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart ``. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component55.SelectedBridgeB0.selectedLeafB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      · exact Krenn.Component55.SelectedBridgeB1.selectedLeafB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component55.SelectedBridgeB2.selectedLeafB2Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component55.SelectedBridgeB3.selectedLeafB3Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      · exact Krenn.Component55.SelectedBridgeB5.selectedLeafB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component55.SelectedBridgeB7.selectedLeafB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])

/-- The frozen carrier subtree rooted at `` has no common zero. -/
theorem subtreeROOTImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 58 → R)
    (rootZero : Krenn.Component55.Root.RootCommonZero values)
    : False := by
  exact rootImpossible values rootZero

#print axioms Krenn.Component55.SelectedSubtreeROOT.subtreeROOTImpossible

end Krenn.Component55.SelectedSubtreeROOT
