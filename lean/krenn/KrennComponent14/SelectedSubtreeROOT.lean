import KrennComponent14.Root
import KrennComponent14.SelectedBridgeB0
import KrennComponent14.SelectedBridgeB1
import KrennComponent14.SelectedBridgeB2
import KrennComponent14.SelectedBridgeB3
import KrennComponent14.SelectedBridgeB4_0_0
import KrennComponent14.SelectedBridgeB4_0_1
import KrennComponent14.SelectedBridgeB4_0_2
import KrennComponent14.SelectedBridgeB4_0_3
import KrennComponent14.SelectedBridgeB4_0_4
import KrennComponent14.SelectedBridgeB4_0_5
import KrennComponent14.SelectedBridgeB4_0_6
import KrennComponent14.SelectedBridgeB4_0_7
import KrennComponent14.SelectedBridgeB4_1_0
import KrennComponent14.SelectedBridgeB4_1_1
import KrennComponent14.SelectedBridgeB4_1_2
import KrennComponent14.SelectedBridgeB4_1_3
import KrennComponent14.SelectedBridgeB4_1_4
import KrennComponent14.SelectedBridgeB4_1_5
import KrennComponent14.SelectedBridgeB4_1_6
import KrennComponent14.SelectedBridgeB4_1_7
import KrennComponent14.SelectedBridgeB4_2
import KrennComponent14.SelectedBridgeB4_3
import KrennComponent14.SelectedBridgeB4_4_0
import KrennComponent14.SelectedBridgeB4_4_1
import KrennComponent14.SelectedBridgeB4_4_2
import KrennComponent14.SelectedBridgeB4_4_3
import KrennComponent14.SelectedBridgeB4_4_4
import KrennComponent14.SelectedBridgeB4_4_5
import KrennComponent14.SelectedBridgeB4_4_6
import KrennComponent14.SelectedBridgeB4_4_7
import KrennComponent14.SelectedBridgeB4_5
import KrennComponent14.SelectedBridgeB4_6
import KrennComponent14.SelectedBridgeB4_7
import KrennComponent14.SelectedBridgeB5
import KrennComponent14.SelectedBridgeB6_0_0
import KrennComponent14.SelectedBridgeB6_0_1
import KrennComponent14.SelectedBridgeB6_0_2
import KrennComponent14.SelectedBridgeB6_0_3
import KrennComponent14.SelectedBridgeB6_0_4
import KrennComponent14.SelectedBridgeB6_0_5
import KrennComponent14.SelectedBridgeB6_0_6
import KrennComponent14.SelectedBridgeB6_0_7
import KrennComponent14.SelectedBridgeB6_1_0
import KrennComponent14.SelectedBridgeB6_1_1
import KrennComponent14.SelectedBridgeB6_1_2
import KrennComponent14.SelectedBridgeB6_1_3
import KrennComponent14.SelectedBridgeB6_1_4
import KrennComponent14.SelectedBridgeB6_1_5
import KrennComponent14.SelectedBridgeB6_1_6
import KrennComponent14.SelectedBridgeB6_1_7
import KrennComponent14.SelectedBridgeB6_2_0_0
import KrennComponent14.SelectedBridgeB6_2_0_1
import KrennComponent14.SelectedBridgeB6_2_0_2
import KrennComponent14.SelectedBridgeB6_2_0_3
import KrennComponent14.SelectedBridgeB6_2_0_4
import KrennComponent14.SelectedBridgeB6_2_0_5
import KrennComponent14.SelectedBridgeB6_2_0_6
import KrennComponent14.SelectedBridgeB6_2_0_7
import KrennComponent14.SelectedBridgeB6_2_1
import KrennComponent14.SelectedBridgeB6_2_2
import KrennComponent14.SelectedBridgeB6_2_3
import KrennComponent14.SelectedBridgeB6_2_4_0
import KrennComponent14.SelectedBridgeB6_2_4_1
import KrennComponent14.SelectedBridgeB6_2_4_2
import KrennComponent14.SelectedBridgeB6_2_4_3
import KrennComponent14.SelectedBridgeB6_2_4_4
import KrennComponent14.SelectedBridgeB6_2_4_5
import KrennComponent14.SelectedBridgeB6_2_4_6
import KrennComponent14.SelectedBridgeB6_2_4_7
import KrennComponent14.SelectedBridgeB6_2_5
import KrennComponent14.SelectedBridgeB6_2_6
import KrennComponent14.SelectedBridgeB6_2_7
import KrennComponent14.SelectedBridgeB6_3
import KrennComponent14.SelectedBridgeB6_4_0
import KrennComponent14.SelectedBridgeB6_4_1
import KrennComponent14.SelectedBridgeB6_4_2
import KrennComponent14.SelectedBridgeB6_4_3
import KrennComponent14.SelectedBridgeB6_4_4
import KrennComponent14.SelectedBridgeB6_4_5
import KrennComponent14.SelectedBridgeB6_4_6
import KrennComponent14.SelectedBridgeB6_4_7
import KrennComponent14.SelectedBridgeB6_5
import KrennComponent14.SelectedBridgeB6_6
import KrennComponent14.SelectedBridgeB6_7
import KrennComponent14.SelectedBridgeB7

namespace Krenn.Component14.SelectedSubtreeROOT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b6.2.0`. -/
theorem nodeB620Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Equation0 : values 53 = 0)
    (d2Equation1 : values 54 = 0)
    (d2Equation2 : values 55 = 0)
    : False := by
  by_cases zeroD3C0 : values 23 = 0
  ·
    by_cases zeroD3C1 : values 26 = 0
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_0_0.selectedLeafB6_2_0_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_0_1.selectedLeafB6_2_0_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 (values 28)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_0_2.selectedLeafB6_2_0_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 (values 26)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_0_3.selectedLeafB6_2_0_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 (values 26)⁻¹ (by simp [zeroD3C1]) (values 28)⁻¹ (by simp [zeroD3C2])
  ·
    by_cases zeroD3C1 : values 26 = 0
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_0_4.selectedLeafB6_2_0_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) zeroD3C1 zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_0_5.selectedLeafB6_2_0_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) zeroD3C1 (values 28)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_0_6.selectedLeafB6_2_0_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) (values 26)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_0_7.selectedLeafB6_2_0_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) (values 26)⁻¹ (by simp [zeroD3C1]) (values 28)⁻¹ (by simp [zeroD3C2])

/-- Exhaustive selected-row reflection for chart `b6.2.4`. -/
theorem nodeB624Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 53 * d2Inverse0 - 1 = 0)
    (d2Equation1 : values 54 = 0)
    (d2Equation2 : values 55 = 0)
    : False := by
  by_cases zeroD3C0 : values 23 = 0
  ·
    by_cases zeroD3C1 : values 26 = 0
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_4_0.selectedLeafB6_2_4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_4_1.selectedLeafB6_2_4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 (values 28)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_4_2.selectedLeafB6_2_4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 (values 26)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_4_3.selectedLeafB6_2_4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 zeroD3C0 (values 26)⁻¹ (by simp [zeroD3C1]) (values 28)⁻¹ (by simp [zeroD3C2])
  ·
    by_cases zeroD3C1 : values 26 = 0
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_4_4.selectedLeafB6_2_4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) zeroD3C1 zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_4_5.selectedLeafB6_2_4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) zeroD3C1 (values 28)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 28 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_4_6.selectedLeafB6_2_4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) (values 26)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component14.SelectedBridgeB6_2_4_7.selectedLeafB6_2_4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Equation1 d2Equation2 (values 23)⁻¹ (by simp [zeroD3C0]) (values 26)⁻¹ (by simp [zeroD3C1]) (values 28)⁻¹ (by simp [zeroD3C2])

/-- Exhaustive selected-row reflection for chart `b4.0`. -/
theorem nodeB40Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_0_0.selectedLeafB4_0_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_0_1.selectedLeafB4_0_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_0_2.selectedLeafB4_0_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_0_3.selectedLeafB4_0_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_0_4.selectedLeafB4_0_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_0_5.selectedLeafB4_0_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_0_6.selectedLeafB4_0_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_0_7.selectedLeafB4_0_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b4.1`. -/
theorem nodeB41Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_1_0.selectedLeafB4_1_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_1_1.selectedLeafB4_1_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_1_2.selectedLeafB4_1_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_1_3.selectedLeafB4_1_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_1_4.selectedLeafB4_1_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_1_5.selectedLeafB4_1_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_1_6.selectedLeafB4_1_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_1_7.selectedLeafB4_1_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b4.4`. -/
theorem nodeB44Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_4_0.selectedLeafB4_4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_4_1.selectedLeafB4_4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_4_2.selectedLeafB4_4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_4_3.selectedLeafB4_4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_4_4.selectedLeafB4_4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_4_5.selectedLeafB4_4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB4_4_6.selectedLeafB4_4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB4_4_7.selectedLeafB4_4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.0`. -/
theorem nodeB60Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_0_0.selectedLeafB6_0_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_0_1.selectedLeafB6_0_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_0_2.selectedLeafB6_0_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_0_3.selectedLeafB6_0_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_0_4.selectedLeafB6_0_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_0_5.selectedLeafB6_0_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_0_6.selectedLeafB6_0_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_0_7.selectedLeafB6_0_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.1`. -/
theorem nodeB61Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 40 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_1_0.selectedLeafB6_1_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_1_1.selectedLeafB6_1_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_1_2.selectedLeafB6_1_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_1_3.selectedLeafB6_1_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_1_4.selectedLeafB6_1_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_1_5.selectedLeafB6_1_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_1_6.selectedLeafB6_1_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_1_7.selectedLeafB6_1_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Equation1 d1Inverse2 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.2`. -/
theorem nodeB62Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 38 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 39 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact nodeB620Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_2_1.selectedLeafB6_2_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_2.selectedLeafB6_2_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_2_3.selectedLeafB6_2_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact nodeB624Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_2_5.selectedLeafB6_2_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_2_6.selectedLeafB6_2_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_2_7.selectedLeafB6_2_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.4`. -/
theorem nodeB64Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 38 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 39 = 0)
    (d1Equation2 : values 40 = 0)
    : False := by
  by_cases zeroD2C0 : values 53 = 0
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_4_0.selectedLeafB6_4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_4_1.selectedLeafB6_4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_4_2.selectedLeafB6_4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_4_3.selectedLeafB6_4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 54 = 0
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_4_4.selectedLeafB6_4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_4_5.selectedLeafB6_4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 55)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 55 = 0
      · exact Krenn.Component14.SelectedBridgeB6_4_6.selectedLeafB6_4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component14.SelectedBridgeB6_4_7.selectedLeafB6_4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 53)⁻¹ (by simp [zeroD2C0]) (values 54)⁻¹ (by simp [zeroD2C1]) (values 55)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
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
      · exact nodeB40Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact nodeB41Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 40)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact Krenn.Component14.SelectedBridgeB4_2.selectedLeafB4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 39)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component14.SelectedBridgeB4_3.selectedLeafB4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 39)⁻¹ (by simp [zeroD1C1]) (values 40)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 39 = 0
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact nodeB44Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component14.SelectedBridgeB4_5.selectedLeafB4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 40)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact Krenn.Component14.SelectedBridgeB4_6.selectedLeafB4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) (values 39)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component14.SelectedBridgeB4_7.selectedLeafB4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) (values 39)⁻¹ (by simp [zeroD1C1]) (values 40)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b6`. -/
theorem nodeB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 38 = 0
  ·
    by_cases zeroD1C1 : values 39 = 0
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact nodeB60Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact nodeB61Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 40)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact nodeB62Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 39)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component14.SelectedBridgeB6_3.selectedLeafB6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 39)⁻¹ (by simp [zeroD1C1]) (values 40)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 39 = 0
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact nodeB64Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component14.SelectedBridgeB6_5.selectedLeafB6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 40)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 40 = 0
      · exact Krenn.Component14.SelectedBridgeB6_6.selectedLeafB6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) (values 39)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component14.SelectedBridgeB6_7.selectedLeafB6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 38)⁻¹ (by simp [zeroD1C0]) (values 39)⁻¹ (by simp [zeroD1C1]) (values 40)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart ``. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component14.SelectedBridgeB0.selectedLeafB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      · exact Krenn.Component14.SelectedBridgeB1.selectedLeafB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component14.SelectedBridgeB2.selectedLeafB2Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component14.SelectedBridgeB3.selectedLeafB3Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      · exact Krenn.Component14.SelectedBridgeB5.selectedLeafB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component14.SelectedBridgeB7.selectedLeafB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])

/-- The frozen carrier subtree rooted at `` has no common zero. -/
theorem subtreeROOTImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 59 → R)
    (rootZero : Krenn.Component14.Root.RootCommonZero values)
    : False := by
  exact rootImpossible values rootZero

#print axioms Krenn.Component14.SelectedSubtreeROOT.subtreeROOTImpossible

end Krenn.Component14.SelectedSubtreeROOT
