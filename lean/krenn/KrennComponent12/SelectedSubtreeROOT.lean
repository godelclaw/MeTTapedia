import KrennComponent12.Root
import KrennComponent12.SelectedBridgeB0
import KrennComponent12.SelectedBridgeB1
import KrennComponent12.SelectedBridgeB2
import KrennComponent12.SelectedBridgeB3
import KrennComponent12.SelectedBridgeB4_0
import KrennComponent12.SelectedBridgeB4_1
import KrennComponent12.SelectedBridgeB4_2
import KrennComponent12.SelectedBridgeB4_3
import KrennComponent12.SelectedBridgeB4_4
import KrennComponent12.SelectedBridgeB4_5
import KrennComponent12.SelectedBridgeB4_6_0
import KrennComponent12.SelectedBridgeB4_6_1
import KrennComponent12.SelectedBridgeB4_6_2
import KrennComponent12.SelectedBridgeB4_6_3
import KrennComponent12.SelectedBridgeB4_6_4
import KrennComponent12.SelectedBridgeB4_6_5
import KrennComponent12.SelectedBridgeB4_6_6
import KrennComponent12.SelectedBridgeB4_6_7_0
import KrennComponent12.SelectedBridgeB4_6_7_1
import KrennComponent12.SelectedBridgeB4_6_7_2
import KrennComponent12.SelectedBridgeB4_6_7_3
import KrennComponent12.SelectedBridgeB4_6_7_4
import KrennComponent12.SelectedBridgeB4_6_7_5
import KrennComponent12.SelectedBridgeB4_6_7_6
import KrennComponent12.SelectedBridgeB4_6_7_7
import KrennComponent12.SelectedBridgeB4_7
import KrennComponent12.SelectedBridgeB5
import KrennComponent12.SelectedBridgeB6
import KrennComponent12.SelectedBridgeB7

namespace Krenn.Component12.SelectedSubtreeROOT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b4.6.7`. -/
theorem nodeB467Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 53 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 54 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 55 * d2Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD3C0 : values 23 = 0
  ·
    by_cases zeroD3C1 : values 25 = 0
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_7_0.selectedLeafB4_6_7_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 zeroD3C1 zeroD3C2
      · exact Krenn.Component12.SelectedBridgeB4_6_7_1.selectedLeafB4_6_7_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 zeroD3C1 (values 28)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_7_2.selectedLeafB4_6_7_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 (values 25)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component12.SelectedBridgeB4_6_7_3.selectedLeafB4_6_7_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 (values 25)⁻¹ (by simp [zeroD3C1]) (values 28)⁻¹ (by simp [zeroD3C2])
  ·
    by_cases zeroD3C1 : values 25 = 0
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_7_4.selectedLeafB4_6_7_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) zeroD3C1 zeroD3C2
      · exact Krenn.Component12.SelectedBridgeB4_6_7_5.selectedLeafB4_6_7_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) zeroD3C1 (values 28)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_7_6.selectedLeafB4_6_7_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) (values 25)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component12.SelectedBridgeB4_6_7_7.selectedLeafB4_6_7_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) (values 25)⁻¹ (by simp [zeroD3C1]) (values 28)⁻¹ (by simp [zeroD3C2])

/-- Exhaustive selected-row reflection for chart `b4.6`. -/
theorem nodeB46Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_0.selectedLeafB4_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component12.SelectedBridgeB4_6_1.selectedLeafB4_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_2.selectedLeafB4_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component12.SelectedBridgeB4_6_3.selectedLeafB4_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_4.selectedLeafB4_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component12.SelectedBridgeB4_6_5.selectedLeafB4_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component12.SelectedBridgeB4_6_6.selectedLeafB4_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact nodeB467Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 38 = 0
  ·
    by_cases zeroD1C1 : values 39 = 0
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact Krenn.Component12.SelectedBridgeB4_0.selectedLeafB4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component12.SelectedBridgeB4_1.selectedLeafB4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 40)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact Krenn.Component12.SelectedBridgeB4_2.selectedLeafB4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 39)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component12.SelectedBridgeB4_3.selectedLeafB4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 39)⁻¹ (by simp [zeroD1C1]) (values 40)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 39 = 0
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact Krenn.Component12.SelectedBridgeB4_4.selectedLeafB4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component12.SelectedBridgeB4_5.selectedLeafB4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 40)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact nodeB46Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) (values 39)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component12.SelectedBridgeB4_7.selectedLeafB4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) (values 39)⁻¹ (by simp [zeroD1C1]) (values 40)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart ``. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component12.SelectedBridgeB0.selectedLeafB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      · exact Krenn.Component12.SelectedBridgeB1.selectedLeafB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component12.SelectedBridgeB2.selectedLeafB2Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component12.SelectedBridgeB3.selectedLeafB3Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      · exact Krenn.Component12.SelectedBridgeB5.selectedLeafB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component12.SelectedBridgeB6.selectedLeafB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component12.SelectedBridgeB7.selectedLeafB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])

/-- The frozen carrier subtree rooted at `` has no common zero. -/
theorem subtreeROOTImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component12.Root.RootCommonZero values)
    : False := by
  exact rootImpossible values rootZero

#print axioms Krenn.Component12.SelectedSubtreeROOT.subtreeROOTImpossible

end Krenn.Component12.SelectedSubtreeROOT
