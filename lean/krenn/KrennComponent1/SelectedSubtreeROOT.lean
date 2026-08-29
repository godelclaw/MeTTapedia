import KrennComponent1.Root
import KrennComponent1.SelectedBridgeB0
import KrennComponent1.SelectedBridgeB1
import KrennComponent1.SelectedBridgeB2
import KrennComponent1.SelectedBridgeB3
import KrennComponent1.SelectedBridgeB4_0
import KrennComponent1.SelectedBridgeB4_1
import KrennComponent1.SelectedBridgeB4_2
import KrennComponent1.SelectedBridgeB4_3
import KrennComponent1.SelectedBridgeB4_4_0
import KrennComponent1.SelectedBridgeB4_4_1
import KrennComponent1.SelectedBridgeB4_4_2
import KrennComponent1.SelectedBridgeB4_4_3
import KrennComponent1.SelectedBridgeB4_4_4
import KrennComponent1.SelectedBridgeB4_4_5
import KrennComponent1.SelectedBridgeB4_4_6
import KrennComponent1.SelectedBridgeB4_4_7
import KrennComponent1.SelectedBridgeB4_5
import KrennComponent1.SelectedBridgeB4_6_0
import KrennComponent1.SelectedBridgeB4_6_1
import KrennComponent1.SelectedBridgeB4_6_2
import KrennComponent1.SelectedBridgeB4_6_3
import KrennComponent1.SelectedBridgeB4_6_4
import KrennComponent1.SelectedBridgeB4_6_5
import KrennComponent1.SelectedBridgeB4_6_6
import KrennComponent1.SelectedBridgeB4_6_7
import KrennComponent1.SelectedBridgeB4_7
import KrennComponent1.SelectedBridgeB5_0
import KrennComponent1.SelectedBridgeB5_1
import KrennComponent1.SelectedBridgeB5_2
import KrennComponent1.SelectedBridgeB5_3
import KrennComponent1.SelectedBridgeB5_4
import KrennComponent1.SelectedBridgeB5_5
import KrennComponent1.SelectedBridgeB5_6_0
import KrennComponent1.SelectedBridgeB5_6_1
import KrennComponent1.SelectedBridgeB5_6_2
import KrennComponent1.SelectedBridgeB5_6_3
import KrennComponent1.SelectedBridgeB5_6_4
import KrennComponent1.SelectedBridgeB5_6_5
import KrennComponent1.SelectedBridgeB5_6_6
import KrennComponent1.SelectedBridgeB5_6_7
import KrennComponent1.SelectedBridgeB5_7
import KrennComponent1.SelectedBridgeB6_0
import KrennComponent1.SelectedBridgeB6_1
import KrennComponent1.SelectedBridgeB6_2_0
import KrennComponent1.SelectedBridgeB6_2_1
import KrennComponent1.SelectedBridgeB6_2_2
import KrennComponent1.SelectedBridgeB6_2_3
import KrennComponent1.SelectedBridgeB6_2_4
import KrennComponent1.SelectedBridgeB6_2_5
import KrennComponent1.SelectedBridgeB6_2_6
import KrennComponent1.SelectedBridgeB6_2_7
import KrennComponent1.SelectedBridgeB6_3
import KrennComponent1.SelectedBridgeB6_4_0
import KrennComponent1.SelectedBridgeB6_4_1
import KrennComponent1.SelectedBridgeB6_4_2
import KrennComponent1.SelectedBridgeB6_4_3
import KrennComponent1.SelectedBridgeB6_4_4
import KrennComponent1.SelectedBridgeB6_4_5
import KrennComponent1.SelectedBridgeB6_4_6
import KrennComponent1.SelectedBridgeB6_4_7
import KrennComponent1.SelectedBridgeB6_5
import KrennComponent1.SelectedBridgeB6_6_0
import KrennComponent1.SelectedBridgeB6_6_1
import KrennComponent1.SelectedBridgeB6_6_2
import KrennComponent1.SelectedBridgeB6_6_3
import KrennComponent1.SelectedBridgeB6_6_4
import KrennComponent1.SelectedBridgeB6_6_5
import KrennComponent1.SelectedBridgeB6_6_6
import KrennComponent1.SelectedBridgeB6_6_7
import KrennComponent1.SelectedBridgeB6_7
import KrennComponent1.SelectedBridgeB7_0
import KrennComponent1.SelectedBridgeB7_1
import KrennComponent1.SelectedBridgeB7_2
import KrennComponent1.SelectedBridgeB7_3
import KrennComponent1.SelectedBridgeB7_4
import KrennComponent1.SelectedBridgeB7_5
import KrennComponent1.SelectedBridgeB7_6_0
import KrennComponent1.SelectedBridgeB7_6_1
import KrennComponent1.SelectedBridgeB7_6_2
import KrennComponent1.SelectedBridgeB7_6_3
import KrennComponent1.SelectedBridgeB7_6_4
import KrennComponent1.SelectedBridgeB7_6_5
import KrennComponent1.SelectedBridgeB7_6_6
import KrennComponent1.SelectedBridgeB7_6_7
import KrennComponent1.SelectedBridgeB7_7

namespace Krenn.Component1.SelectedSubtreeROOT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b4.4`. -/
theorem nodeB44Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 51 = 0
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_4_0.selectedLeafB4_4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_4_1.selectedLeafB4_4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_4_2.selectedLeafB4_4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_4_3.selectedLeafB4_4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_4_4.selectedLeafB4_4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_4_5.selectedLeafB4_4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_4_6.selectedLeafB4_4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_4_7.selectedLeafB4_4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b4.6`. -/
theorem nodeB46Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 51 = 0
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_6_0.selectedLeafB4_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_6_1.selectedLeafB4_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_6_2.selectedLeafB4_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_6_3.selectedLeafB4_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_6_4.selectedLeafB4_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_6_5.selectedLeafB4_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB4_6_6.selectedLeafB4_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB4_6_7.selectedLeafB4_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b5.6`. -/
theorem nodeB56Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 51 = 0
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB5_6_0.selectedLeafB5_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB5_6_1.selectedLeafB5_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB5_6_2.selectedLeafB5_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB5_6_3.selectedLeafB5_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB5_6_4.selectedLeafB5_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB5_6_5.selectedLeafB5_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB5_6_6.selectedLeafB5_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB5_6_7.selectedLeafB5_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.2`. -/
theorem nodeB62Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 40 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 51 = 0
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_2_0.selectedLeafB6_2_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_2_1.selectedLeafB6_2_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_2_2.selectedLeafB6_2_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_2_3.selectedLeafB6_2_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_2_4.selectedLeafB6_2_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_2_5.selectedLeafB6_2_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_2_6.selectedLeafB6_2_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_2_7.selectedLeafB6_2_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.4`. -/
theorem nodeB64Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Equation1 : values 41 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 51 = 0
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_4_0.selectedLeafB6_4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_4_1.selectedLeafB6_4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_4_2.selectedLeafB6_4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_4_3.selectedLeafB6_4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_4_4.selectedLeafB6_4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_4_5.selectedLeafB6_4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_4_6.selectedLeafB6_4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_4_7.selectedLeafB6_4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b6.6`. -/
theorem nodeB66Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 51 = 0
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_6_0.selectedLeafB6_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_6_1.selectedLeafB6_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_6_2.selectedLeafB6_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_6_3.selectedLeafB6_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_6_4.selectedLeafB6_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_6_5.selectedLeafB6_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB6_6_6.selectedLeafB6_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB6_6_7.selectedLeafB6_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b7.6`. -/
theorem nodeB76Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 40 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 41 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 42 = 0)
    : False := by
  by_cases zeroD2C0 : values 51 = 0
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB7_6_0.selectedLeafB7_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB7_6_1.selectedLeafB7_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB7_6_2.selectedLeafB7_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB7_6_3.selectedLeafB7_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 52 = 0
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB7_6_4.selectedLeafB7_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB7_6_5.selectedLeafB7_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 53)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 53 = 0
      · exact Krenn.Component1.SelectedBridgeB7_6_6.selectedLeafB7_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component1.SelectedBridgeB7_6_7.selectedLeafB7_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 51)⁻¹ (by simp [zeroD2C0]) (values 52)⁻¹ (by simp [zeroD2C1]) (values 53)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB4_0.selectedLeafB4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB4_1.selectedLeafB4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB4_2.selectedLeafB4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB4_3.selectedLeafB4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB44Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB4_5.selectedLeafB4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB46Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB4_7.selectedLeafB4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b5`. -/
theorem nodeB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB5_0.selectedLeafB5_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB5_1.selectedLeafB5_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB5_2.selectedLeafB5_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB5_3.selectedLeafB5_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB5_4.selectedLeafB5_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB5_5.selectedLeafB5_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB56Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB5_7.selectedLeafB5_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b6`. -/
theorem nodeB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB6_0.selectedLeafB6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB6_1.selectedLeafB6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB62Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB6_3.selectedLeafB6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB64Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB6_5.selectedLeafB6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB66Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB6_7.selectedLeafB6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b7`. -/
theorem nodeB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 40 = 0
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB7_0.selectedLeafB7_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB7_1.selectedLeafB7_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB7_2.selectedLeafB7_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB7_3.selectedLeafB7_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 41 = 0
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact Krenn.Component1.SelectedBridgeB7_4.selectedLeafB7_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB7_5.selectedLeafB7_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 42)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 42 = 0
      · exact nodeB76Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component1.SelectedBridgeB7_7.selectedLeafB7_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 40)⁻¹ (by simp [zeroD1C0]) (values 41)⁻¹ (by simp [zeroD1C1]) (values 42)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart ``. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component1.SelectedBridgeB0.selectedLeafB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      · exact Krenn.Component1.SelectedBridgeB1.selectedLeafB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact Krenn.Component1.SelectedBridgeB2.selectedLeafB2Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact Krenn.Component1.SelectedBridgeB3.selectedLeafB3Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB4Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 zeroD0C2
      · exact nodeB5Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB6Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact nodeB7Impossible values rootZero (values 0)⁻¹ (by simp [zeroD0C0]) (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])

/-- The frozen carrier subtree rooted at `` has no common zero. -/
theorem subtreeROOTImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 57 → R)
    (rootZero : Krenn.Component1.Root.RootCommonZero values)
    : False := by
  exact rootImpossible values rootZero

#print axioms Krenn.Component1.SelectedSubtreeROOT.subtreeROOTImpossible

end Krenn.Component1.SelectedSubtreeROOT
