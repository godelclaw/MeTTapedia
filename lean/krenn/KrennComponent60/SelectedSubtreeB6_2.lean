import KrennComponent60.Root
import KrennComponent60.SelectedBridgeB6_2_0
import KrennComponent60.SelectedBridgeB6_2_1
import KrennComponent60.SelectedBridgeB6_2_2
import KrennComponent60.SelectedBridgeB6_2_3_0
import KrennComponent60.SelectedBridgeB6_2_3_1
import KrennComponent60.SelectedBridgeB6_2_3_2
import KrennComponent60.SelectedBridgeB6_2_3_3
import KrennComponent60.SelectedBridgeB6_2_3_4
import KrennComponent60.SelectedBridgeB6_2_3_5
import KrennComponent60.SelectedBridgeB6_2_3_6
import KrennComponent60.SelectedBridgeB6_2_3_7
import KrennComponent60.SelectedBridgeB6_2_4
import KrennComponent60.SelectedBridgeB6_2_5
import KrennComponent60.SelectedBridgeB6_2_6_0
import KrennComponent60.SelectedBridgeB6_2_6_1
import KrennComponent60.SelectedBridgeB6_2_6_2
import KrennComponent60.SelectedBridgeB6_2_6_3
import KrennComponent60.SelectedBridgeB6_2_6_4_0
import KrennComponent60.SelectedBridgeB6_2_6_4_1
import KrennComponent60.SelectedBridgeB6_2_6_4_2
import KrennComponent60.SelectedBridgeB6_2_6_4_3
import KrennComponent60.SelectedBridgeB6_2_6_4_4
import KrennComponent60.SelectedBridgeB6_2_6_4_5
import KrennComponent60.SelectedBridgeB6_2_6_4_6
import KrennComponent60.SelectedBridgeB6_2_6_4_7
import KrennComponent60.SelectedBridgeB6_2_6_5
import KrennComponent60.SelectedBridgeB6_2_6_6_0
import KrennComponent60.SelectedBridgeB6_2_6_6_1
import KrennComponent60.SelectedBridgeB6_2_6_6_2
import KrennComponent60.SelectedBridgeB6_2_6_6_3
import KrennComponent60.SelectedBridgeB6_2_6_6_4
import KrennComponent60.SelectedBridgeB6_2_6_6_5
import KrennComponent60.SelectedBridgeB6_2_6_6_6
import KrennComponent60.SelectedBridgeB6_2_6_6_7
import KrennComponent60.SelectedBridgeB6_2_6_7
import KrennComponent60.SelectedBridgeB6_2_7

namespace Krenn.Component60.SelectedSubtreeB6_2

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b6.2.6.4`. -/
theorem nodeB6264Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Equation1 : values 28 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  by_cases zeroD4C0 : values 58 = 0
  ·
    by_cases zeroD4C1 : values 59 = 0
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_0.selectedLeafB6_2_6_4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_1.selectedLeafB6_2_6_4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_2.selectedLeafB6_2_6_4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_3.selectedLeafB6_2_6_4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])
  ·
    by_cases zeroD4C1 : values 59 = 0
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_4.selectedLeafB6_2_6_4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_5.selectedLeafB6_2_6_4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_6.selectedLeafB6_2_6_4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_4_7.selectedLeafB6_2_6_4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])

/-- Exhaustive selected-row reflection for chart `b6.2.6.6`. -/
theorem nodeB6266Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    (d3Inverse0 : R)
    (d3Equation0 : values 25 * d3Inverse0 - 1 = 0)
    (d3Inverse1 : R)
    (d3Equation1 : values 28 * d3Inverse1 - 1 = 0)
    (d3Equation2 : values 29 = 0)
    : False := by
  by_cases zeroD4C0 : values 58 = 0
  ·
    by_cases zeroD4C1 : values 59 = 0
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_0.selectedLeafB6_2_6_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_1.selectedLeafB6_2_6_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_2.selectedLeafB6_2_6_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_3.selectedLeafB6_2_6_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])
  ·
    by_cases zeroD4C1 : values 59 = 0
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_4.selectedLeafB6_2_6_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_5.selectedLeafB6_2_6_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_6.selectedLeafB6_2_6_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_6_7.selectedLeafB6_2_6_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])

/-- Exhaustive selected-row reflection for chart `b6.2.3`. -/
theorem nodeB623Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Inverse2 : R)
    (d2Equation2 : values 57 * d2Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD3C0 : values 25 = 0
  ·
    by_cases zeroD3C1 : values 28 = 0
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_3_0.selectedLeafB6_2_3_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 zeroD3C1 zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_3_1.selectedLeafB6_2_3_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 zeroD3C1 (values 29)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_3_2.selectedLeafB6_2_3_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 (values 28)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_3_3.selectedLeafB6_2_3_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 zeroD3C0 (values 28)⁻¹ (by simp [zeroD3C1]) (values 29)⁻¹ (by simp [zeroD3C2])
  ·
    by_cases zeroD3C1 : values 28 = 0
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_3_4.selectedLeafB6_2_3_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) zeroD3C1 zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_3_5.selectedLeafB6_2_3_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) zeroD3C1 (values 29)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_3_6.selectedLeafB6_2_3_6Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) (values 28)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_3_7.selectedLeafB6_2_3_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Inverse2 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) (values 28)⁻¹ (by simp [zeroD3C1]) (values 29)⁻¹ (by simp [zeroD3C2])

/-- Exhaustive selected-row reflection for chart `b6.2.6`. -/
theorem nodeB626Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Inverse1 : R)
    (d0Equation1 : values 1 * d0Inverse1 - 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Inverse0 : R)
    (d2Equation0 : values 55 * d2Inverse0 - 1 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  by_cases zeroD3C0 : values 25 = 0
  ·
    by_cases zeroD3C1 : values 28 = 0
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_0.selectedLeafB6_2_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_1.selectedLeafB6_2_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 (values 29)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_6_2.selectedLeafB6_2_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 (values 28)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_3.selectedLeafB6_2_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 (values 28)⁻¹ (by simp [zeroD3C1]) (values 29)⁻¹ (by simp [zeroD3C2])
  ·
    by_cases zeroD3C1 : values 28 = 0
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact nodeB6264Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) zeroD3C1 zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_5.selectedLeafB6_2_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) zeroD3C1 (values 29)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact nodeB6266Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) (values 28)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB6_2_6_7.selectedLeafB6_2_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Inverse0 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) (values 28)⁻¹ (by simp [zeroD3C1]) (values 29)⁻¹ (by simp [zeroD3C2])

/-- Exhaustive selected-row reflection for chart `b6.2`. -/
theorem nodeB62Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
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
  by_cases zeroD2C0 : values 55 = 0
  ·
    by_cases zeroD2C1 : values 56 = 0
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_0.selectedLeafB6_2_0Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component60.SelectedBridgeB6_2_1.selectedLeafB6_2_1Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 zeroD2C1 (values 57)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_2.selectedLeafB6_2_2Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 56)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact nodeB623Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 zeroD2C0 (values 56)⁻¹ (by simp [zeroD2C1]) (values 57)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 56 = 0
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact Krenn.Component60.SelectedBridgeB6_2_4.selectedLeafB6_2_4Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component60.SelectedBridgeB6_2_5.selectedLeafB6_2_5Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 57)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact nodeB626Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) (values 56)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component60.SelectedBridgeB6_2_7.selectedLeafB6_2_7Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) (values 56)⁻¹ (by simp [zeroD2C1]) (values 57)⁻¹ (by simp [zeroD2C2])

/-- The frozen carrier subtree rooted at `b6.2` has no common zero. -/
theorem subtreeB6_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
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
  exact nodeB62Impossible values rootZero d0Inverse0 d0Equation0 d0Inverse1 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2

#print axioms Krenn.Component60.SelectedSubtreeB6_2.subtreeB6_2Impossible

end Krenn.Component60.SelectedSubtreeB6_2
