import KrennComponent10.Root
import KrennComponent10.SelectedBridgeB0_0
import KrennComponent10.SelectedBridgeB0_1
import KrennComponent10.SelectedBridgeB0_2_0
import KrennComponent10.SelectedBridgeB0_2_1
import KrennComponent10.SelectedBridgeB0_2_2
import KrennComponent10.SelectedBridgeB0_2_3
import KrennComponent10.SelectedBridgeB0_2_4
import KrennComponent10.SelectedBridgeB0_2_5
import KrennComponent10.SelectedBridgeB0_2_6
import KrennComponent10.SelectedBridgeB0_2_7
import KrennComponent10.SelectedBridgeB0_3
import KrennComponent10.SelectedBridgeB0_4
import KrennComponent10.SelectedBridgeB0_5
import KrennComponent10.SelectedBridgeB0_6_0
import KrennComponent10.SelectedBridgeB0_6_1
import KrennComponent10.SelectedBridgeB0_6_2
import KrennComponent10.SelectedBridgeB0_6_3
import KrennComponent10.SelectedBridgeB0_6_4
import KrennComponent10.SelectedBridgeB0_6_5
import KrennComponent10.SelectedBridgeB0_6_6
import KrennComponent10.SelectedBridgeB0_6_7
import KrennComponent10.SelectedBridgeB0_7
import KrennComponent10.SelectedBridgeB1_0
import KrennComponent10.SelectedBridgeB1_1
import KrennComponent10.SelectedBridgeB1_2
import KrennComponent10.SelectedBridgeB1_3
import KrennComponent10.SelectedBridgeB1_4
import KrennComponent10.SelectedBridgeB1_5
import KrennComponent10.SelectedBridgeB1_6_0
import KrennComponent10.SelectedBridgeB1_6_1
import KrennComponent10.SelectedBridgeB1_6_2
import KrennComponent10.SelectedBridgeB1_6_3
import KrennComponent10.SelectedBridgeB1_6_4
import KrennComponent10.SelectedBridgeB1_6_5
import KrennComponent10.SelectedBridgeB1_6_6
import KrennComponent10.SelectedBridgeB1_6_7
import KrennComponent10.SelectedBridgeB1_7
import KrennComponent10.SelectedBridgeB2_0
import KrennComponent10.SelectedBridgeB2_1
import KrennComponent10.SelectedBridgeB2_2_0
import KrennComponent10.SelectedBridgeB2_2_1
import KrennComponent10.SelectedBridgeB2_2_2
import KrennComponent10.SelectedBridgeB2_2_3
import KrennComponent10.SelectedBridgeB2_2_4
import KrennComponent10.SelectedBridgeB2_2_5
import KrennComponent10.SelectedBridgeB2_2_6
import KrennComponent10.SelectedBridgeB2_2_7
import KrennComponent10.SelectedBridgeB2_3
import KrennComponent10.SelectedBridgeB2_4
import KrennComponent10.SelectedBridgeB2_5
import KrennComponent10.SelectedBridgeB2_6_0
import KrennComponent10.SelectedBridgeB2_6_1
import KrennComponent10.SelectedBridgeB2_6_2
import KrennComponent10.SelectedBridgeB2_6_3
import KrennComponent10.SelectedBridgeB2_6_4
import KrennComponent10.SelectedBridgeB2_6_5
import KrennComponent10.SelectedBridgeB2_6_6
import KrennComponent10.SelectedBridgeB2_6_7
import KrennComponent10.SelectedBridgeB2_7
import KrennComponent10.SelectedBridgeB3_0
import KrennComponent10.SelectedBridgeB3_1
import KrennComponent10.SelectedBridgeB3_2
import KrennComponent10.SelectedBridgeB3_3
import KrennComponent10.SelectedBridgeB3_4
import KrennComponent10.SelectedBridgeB3_5
import KrennComponent10.SelectedBridgeB3_6
import KrennComponent10.SelectedBridgeB3_7
import KrennComponent10.SelectedBridgeB4_0
import KrennComponent10.SelectedBridgeB4_1
import KrennComponent10.SelectedBridgeB4_2
import KrennComponent10.SelectedBridgeB4_3
import KrennComponent10.SelectedBridgeB4_4
import KrennComponent10.SelectedBridgeB4_5
import KrennComponent10.SelectedBridgeB4_6
import KrennComponent10.SelectedBridgeB4_7
import KrennComponent10.SelectedBridgeB5_0
import KrennComponent10.SelectedBridgeB5_1
import KrennComponent10.SelectedBridgeB5_2
import KrennComponent10.SelectedBridgeB5_3
import KrennComponent10.SelectedBridgeB5_4
import KrennComponent10.SelectedBridgeB5_5
import KrennComponent10.SelectedBridgeB5_6_0
import KrennComponent10.SelectedBridgeB5_6_1
import KrennComponent10.SelectedBridgeB5_6_2
import KrennComponent10.SelectedBridgeB5_6_3
import KrennComponent10.SelectedBridgeB5_6_4
import KrennComponent10.SelectedBridgeB5_6_5
import KrennComponent10.SelectedBridgeB5_6_6
import KrennComponent10.SelectedBridgeB5_6_7
import KrennComponent10.SelectedBridgeB5_7
import KrennComponent10.SelectedBridgeB6_0
import KrennComponent10.SelectedBridgeB6_1
import KrennComponent10.SelectedBridgeB6_2
import KrennComponent10.SelectedBridgeB6_3
import KrennComponent10.SelectedBridgeB6_4
import KrennComponent10.SelectedBridgeB6_5
import KrennComponent10.SelectedBridgeB6_6
import KrennComponent10.SelectedBridgeB6_7
import KrennComponent10.SelectedBridgeB7_0
import KrennComponent10.SelectedBridgeB7_1
import KrennComponent10.SelectedBridgeB7_2
import KrennComponent10.SelectedBridgeB7_3
import KrennComponent10.SelectedBridgeB7_4
import KrennComponent10.SelectedBridgeB7_5
import KrennComponent10.SelectedBridgeB7_6
import KrennComponent10.SelectedBridgeB7_7

namespace Krenn.Component10.SelectedSubtreeROOT

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b0.2`. -/
theorem nodeB02Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 54 = 0
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_2_0.selectedLeafB0_2_0Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_2_1.selectedLeafB0_2_1Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_2_2.selectedLeafB0_2_2Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_2_3.selectedLeafB0_2_3Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_2_4.selectedLeafB0_2_4Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_2_5.selectedLeafB0_2_5Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_2_6.selectedLeafB0_2_6Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_2_7.selectedLeafB0_2_7Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b0.6`. -/
theorem nodeB06Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 54 = 0
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_6_0.selectedLeafB0_6_0Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_6_1.selectedLeafB0_6_1Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_6_2.selectedLeafB0_6_2Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_6_3.selectedLeafB0_6_3Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_6_4.selectedLeafB0_6_4Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_6_5.selectedLeafB0_6_5Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB0_6_6.selectedLeafB0_6_6Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB0_6_7.selectedLeafB0_6_7Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b1.6`. -/
theorem nodeB16Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 54 = 0
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB1_6_0.selectedLeafB1_6_0Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB1_6_1.selectedLeafB1_6_1Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB1_6_2.selectedLeafB1_6_2Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB1_6_3.selectedLeafB1_6_3Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB1_6_4.selectedLeafB1_6_4Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB1_6_5.selectedLeafB1_6_5Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB1_6_6.selectedLeafB1_6_6Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB1_6_7.selectedLeafB1_6_7Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b2.2`. -/
theorem nodeB22Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 54 = 0
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_2_0.selectedLeafB2_2_0Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_2_1.selectedLeafB2_2_1Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_2_2.selectedLeafB2_2_2Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_2_3.selectedLeafB2_2_3Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_2_4.selectedLeafB2_2_4Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_2_5.selectedLeafB2_2_5Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_2_6.selectedLeafB2_2_6Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_2_7.selectedLeafB2_2_7Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b2.6`. -/
theorem nodeB26Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 54 = 0
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_6_0.selectedLeafB2_6_0Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_6_1.selectedLeafB2_6_1Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_6_2.selectedLeafB2_6_2Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_6_3.selectedLeafB2_6_3Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_6_4.selectedLeafB2_6_4Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_6_5.selectedLeafB2_6_5Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB2_6_6.selectedLeafB2_6_6Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB2_6_7.selectedLeafB2_6_7Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b5.6`. -/
theorem nodeB56Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    (d1Inverse0 : R)
    (d1Equation0 : values 39 * d1Inverse0 - 1 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    : False := by
  by_cases zeroD2C0 : values 54 = 0
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB5_6_0.selectedLeafB5_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB5_6_1.selectedLeafB5_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB5_6_2.selectedLeafB5_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB5_6_3.selectedLeafB5_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 55 = 0
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB5_6_4.selectedLeafB5_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB5_6_5.selectedLeafB5_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 56)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 56 = 0
      · exact Krenn.Component10.SelectedBridgeB5_6_6.selectedLeafB5_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component10.SelectedBridgeB5_6_7.selectedLeafB5_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 d1Inverse0 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 54)⁻¹ (by simp [zeroD2C0]) (values 55)⁻¹ (by simp [zeroD2C1]) (values 56)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b0`. -/
theorem nodeB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB0_0.selectedLeafB0_0Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB0_1.selectedLeafB0_1Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB02Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB0_3.selectedLeafB0_3Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB0_4.selectedLeafB0_4Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB0_5.selectedLeafB0_5Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB06Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB0_7.selectedLeafB0_7Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b1`. -/
theorem nodeB1Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB1_0.selectedLeafB1_0Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB1_1.selectedLeafB1_1Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB1_2.selectedLeafB1_2Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB1_3.selectedLeafB1_3Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB1_4.selectedLeafB1_4Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB1_5.selectedLeafB1_5Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB16Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB1_7.selectedLeafB1_7Impossible values rootZero d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b2`. -/
theorem nodeB2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB2_0.selectedLeafB2_0Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB2_1.selectedLeafB2_1Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB22Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB2_3.selectedLeafB2_3Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB2_4.selectedLeafB2_4Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB2_5.selectedLeafB2_5Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB26Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB2_7.selectedLeafB2_7Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b3`. -/
theorem nodeB3Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB3_0.selectedLeafB3_0Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB3_1.selectedLeafB3_1Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB3_2.selectedLeafB3_2Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB3_3.selectedLeafB3_3Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB3_4.selectedLeafB3_4Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB3_5.selectedLeafB3_5Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB3_6.selectedLeafB3_6Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB3_7.selectedLeafB3_7Impossible values rootZero d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b4`. -/
theorem nodeB4Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
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
      · exact Krenn.Component10.SelectedBridgeB4_0.selectedLeafB4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB4_1.selectedLeafB4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB4_2.selectedLeafB4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB4_3.selectedLeafB4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB4_4.selectedLeafB4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB4_5.selectedLeafB4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB4_6.selectedLeafB4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB4_7.selectedLeafB4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b5`. -/
theorem nodeB5Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB5_0.selectedLeafB5_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB5_1.selectedLeafB5_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB5_2.selectedLeafB5_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB5_3.selectedLeafB5_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB5_4.selectedLeafB5_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB5_5.selectedLeafB5_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact nodeB56Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB5_7.selectedLeafB5_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b6`. -/
theorem nodeB6Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
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
      · exact Krenn.Component10.SelectedBridgeB6_0.selectedLeafB6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB6_1.selectedLeafB6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB6_2.selectedLeafB6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB6_3.selectedLeafB6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB6_4.selectedLeafB6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB6_5.selectedLeafB6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB6_6.selectedLeafB6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB6_7.selectedLeafB6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart `b7`. -/
theorem nodeB7Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Inverse2 : R)
    (d0Equation2 : values 2 * d0Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB7_0.selectedLeafB7_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB7_1.selectedLeafB7_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB7_2.selectedLeafB7_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB7_3.selectedLeafB7_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB7_4.selectedLeafB7_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB7_5.selectedLeafB7_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component10.SelectedBridgeB7_6.selectedLeafB7_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component10.SelectedBridgeB7_7.selectedLeafB7_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Inverse2 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- Exhaustive selected-row reflection for chart ``. -/
theorem rootImpossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    : False := by
  by_cases zeroD0C0 : values 0 = 0
  ·
    by_cases zeroD0C1 : values 1 = 0
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB0Impossible values rootZero zeroD0C0 zeroD0C1 zeroD0C2
      · exact nodeB1Impossible values rootZero zeroD0C0 zeroD0C1 (values 2)⁻¹ (by simp [zeroD0C2])
    ·
      by_cases zeroD0C2 : values 2 = 0
      · exact nodeB2Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) zeroD0C2
      · exact nodeB3Impossible values rootZero zeroD0C0 (values 1)⁻¹ (by simp [zeroD0C1]) (values 2)⁻¹ (by simp [zeroD0C2])
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
    (values : Fin 60 → R)
    (rootZero : Krenn.Component10.Root.RootCommonZero values)
    : False := by
  exact rootImpossible values rootZero

#print axioms Krenn.Component10.SelectedSubtreeROOT.subtreeROOTImpossible

end Krenn.Component10.SelectedSubtreeROOT
