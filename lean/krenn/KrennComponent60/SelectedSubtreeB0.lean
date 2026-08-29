import KrennComponent60.Root
import KrennComponent60.SelectedBridgeB0_0
import KrennComponent60.SelectedBridgeB0_1
import KrennComponent60.SelectedBridgeB0_2
import KrennComponent60.SelectedBridgeB0_3_0
import KrennComponent60.SelectedBridgeB0_3_1
import KrennComponent60.SelectedBridgeB0_3_2
import KrennComponent60.SelectedBridgeB0_3_3
import KrennComponent60.SelectedBridgeB0_3_4
import KrennComponent60.SelectedBridgeB0_3_5
import KrennComponent60.SelectedBridgeB0_3_6
import KrennComponent60.SelectedBridgeB0_3_7
import KrennComponent60.SelectedBridgeB0_4
import KrennComponent60.SelectedBridgeB0_5
import KrennComponent60.SelectedBridgeB0_6
import KrennComponent60.SelectedBridgeB0_7

namespace Krenn.Component60.SelectedSubtreeB0

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b0.3`. -/
theorem nodeB03Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Inverse2 : R)
    (d1Equation2 : values 41 * d1Inverse2 - 1 = 0)
    : False := by
  by_cases zeroD2C0 : values 55 = 0
  ·
    by_cases zeroD2C1 : values 56 = 0
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact Krenn.Component60.SelectedBridgeB0_3_0.selectedLeafB0_3_0Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 zeroD2C2
      · exact Krenn.Component60.SelectedBridgeB0_3_1.selectedLeafB0_3_1Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 zeroD2C1 (values 57)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact Krenn.Component60.SelectedBridgeB0_3_2.selectedLeafB0_3_2Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 56)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component60.SelectedBridgeB0_3_3.selectedLeafB0_3_3Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 zeroD2C0 (values 56)⁻¹ (by simp [zeroD2C1]) (values 57)⁻¹ (by simp [zeroD2C2])
  ·
    by_cases zeroD2C1 : values 56 = 0
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact Krenn.Component60.SelectedBridgeB0_3_4.selectedLeafB0_3_4Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) zeroD2C1 zeroD2C2
      · exact Krenn.Component60.SelectedBridgeB0_3_5.selectedLeafB0_3_5Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) zeroD2C1 (values 57)⁻¹ (by simp [zeroD2C2])
    ·
      by_cases zeroD2C2 : values 57 = 0
      · exact Krenn.Component60.SelectedBridgeB0_3_6.selectedLeafB0_3_6Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) (values 56)⁻¹ (by simp [zeroD2C1]) zeroD2C2
      · exact Krenn.Component60.SelectedBridgeB0_3_7.selectedLeafB0_3_7Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Inverse2 d1Equation2 (values 55)⁻¹ (by simp [zeroD2C0]) (values 56)⁻¹ (by simp [zeroD2C1]) (values 57)⁻¹ (by simp [zeroD2C2])

/-- Exhaustive selected-row reflection for chart `b0`. -/
theorem nodeB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  by_cases zeroD1C0 : values 39 = 0
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component60.SelectedBridgeB0_0.selectedLeafB0_0Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 zeroD1C2
      · exact Krenn.Component60.SelectedBridgeB0_1.selectedLeafB0_1Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component60.SelectedBridgeB0_2.selectedLeafB0_2Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact nodeB03Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 zeroD1C0 (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])
  ·
    by_cases zeroD1C1 : values 40 = 0
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component60.SelectedBridgeB0_4.selectedLeafB0_4Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 zeroD1C2
      · exact Krenn.Component60.SelectedBridgeB0_5.selectedLeafB0_5Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) zeroD1C1 (values 41)⁻¹ (by simp [zeroD1C2])
    ·
      by_cases zeroD1C2 : values 41 = 0
      · exact Krenn.Component60.SelectedBridgeB0_6.selectedLeafB0_6Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) zeroD1C2
      · exact Krenn.Component60.SelectedBridgeB0_7.selectedLeafB0_7Impossible values rootZero d0Equation0 d0Equation1 d0Equation2 (values 39)⁻¹ (by simp [zeroD1C0]) (values 40)⁻¹ (by simp [zeroD1C1]) (values 41)⁻¹ (by simp [zeroD1C2])

/-- The frozen carrier subtree rooted at `b0` has no common zero. -/
theorem subtreeB0Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Equation0 : values 0 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    : False := by
  exact nodeB0Impossible values rootZero d0Equation0 d0Equation1 d0Equation2

#print axioms Krenn.Component60.SelectedSubtreeB0.subtreeB0Impossible

end Krenn.Component60.SelectedSubtreeB0
