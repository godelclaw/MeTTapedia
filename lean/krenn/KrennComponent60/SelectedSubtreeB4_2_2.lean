import KrennComponent60.Root
import KrennComponent60.SelectedBridgeB4_2_2_0
import KrennComponent60.SelectedBridgeB4_2_2_1
import KrennComponent60.SelectedBridgeB4_2_2_2
import KrennComponent60.SelectedBridgeB4_2_2_3
import KrennComponent60.SelectedBridgeB4_2_2_4_0
import KrennComponent60.SelectedBridgeB4_2_2_4_1
import KrennComponent60.SelectedBridgeB4_2_2_4_2
import KrennComponent60.SelectedBridgeB4_2_2_4_3
import KrennComponent60.SelectedBridgeB4_2_2_4_4
import KrennComponent60.SelectedBridgeB4_2_2_4_5
import KrennComponent60.SelectedBridgeB4_2_2_4_6
import KrennComponent60.SelectedBridgeB4_2_2_4_7
import KrennComponent60.SelectedBridgeB4_2_2_5
import KrennComponent60.SelectedBridgeB4_2_2_6_0
import KrennComponent60.SelectedBridgeB4_2_2_6_1
import KrennComponent60.SelectedBridgeB4_2_2_6_2
import KrennComponent60.SelectedBridgeB4_2_2_6_3
import KrennComponent60.SelectedBridgeB4_2_2_6_4
import KrennComponent60.SelectedBridgeB4_2_2_6_5
import KrennComponent60.SelectedBridgeB4_2_2_6_6
import KrennComponent60.SelectedBridgeB4_2_2_6_7
import KrennComponent60.SelectedBridgeB4_2_2_7

namespace Krenn.Component60.SelectedSubtreeB4_2_2

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

/-- Exhaustive selected-row reflection for chart `b4.2.2.4`. -/
theorem nodeB4224Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 55 = 0)
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
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_0.selectedLeafB4_2_2_4_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_1.selectedLeafB4_2_2_4_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_2.selectedLeafB4_2_2_4_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_3.selectedLeafB4_2_2_4_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])
  ·
    by_cases zeroD4C1 : values 59 = 0
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_4.selectedLeafB4_2_2_4_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_5.selectedLeafB4_2_2_4_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_6.selectedLeafB4_2_2_4_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_4_7.selectedLeafB4_2_2_4_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])

/-- Exhaustive selected-row reflection for chart `b4.2.2.6`. -/
theorem nodeB4226Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 55 = 0)
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
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_0.selectedLeafB4_2_2_6_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_1.selectedLeafB4_2_2_6_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_2.selectedLeafB4_2_2_6_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_3.selectedLeafB4_2_2_6_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 zeroD4C0 (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])
  ·
    by_cases zeroD4C1 : values 59 = 0
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_4.selectedLeafB4_2_2_6_4Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_5.selectedLeafB4_2_2_6_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) zeroD4C1 (values 60)⁻¹ (by simp [zeroD4C2])
    ·
      by_cases zeroD4C2 : values 60 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_6.selectedLeafB4_2_2_6_6Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) zeroD4C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_6_7.selectedLeafB4_2_2_6_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 d3Inverse0 d3Equation0 d3Inverse1 d3Equation1 d3Equation2 (values 58)⁻¹ (by simp [zeroD4C0]) (values 59)⁻¹ (by simp [zeroD4C1]) (values 60)⁻¹ (by simp [zeroD4C2])

/-- Exhaustive selected-row reflection for chart `b4.2.2`. -/
theorem nodeB422Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  by_cases zeroD3C0 : values 25 = 0
  ·
    by_cases zeroD3C1 : values 28 = 0
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_0.selectedLeafB4_2_2_0Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_1.selectedLeafB4_2_2_1Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 zeroD3C1 (values 29)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact Krenn.Component60.SelectedBridgeB4_2_2_2.selectedLeafB4_2_2_2Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 (values 28)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_3.selectedLeafB4_2_2_3Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 zeroD3C0 (values 28)⁻¹ (by simp [zeroD3C1]) (values 29)⁻¹ (by simp [zeroD3C2])
  ·
    by_cases zeroD3C1 : values 28 = 0
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact nodeB4224Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) zeroD3C1 zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_5.selectedLeafB4_2_2_5Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) zeroD3C1 (values 29)⁻¹ (by simp [zeroD3C2])
    ·
      by_cases zeroD3C2 : values 29 = 0
      · exact nodeB4226Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) (values 28)⁻¹ (by simp [zeroD3C1]) zeroD3C2
      · exact Krenn.Component60.SelectedBridgeB4_2_2_7.selectedLeafB4_2_2_7Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2 (values 25)⁻¹ (by simp [zeroD3C0]) (values 28)⁻¹ (by simp [zeroD3C1]) (values 29)⁻¹ (by simp [zeroD3C2])

/-- The frozen carrier subtree rooted at `b4.2.2` has no common zero. -/
theorem subtreeB4_2_2Impossible {R : Type*} [Field R] [CharZero R]
    (values : Fin 61 → R)
    (rootZero : Krenn.Component60.Root.RootCommonZero values)
    (d0Inverse0 : R)
    (d0Equation0 : values 0 * d0Inverse0 - 1 = 0)
    (d0Equation1 : values 1 = 0)
    (d0Equation2 : values 2 = 0)
    (d1Equation0 : values 39 = 0)
    (d1Inverse1 : R)
    (d1Equation1 : values 40 * d1Inverse1 - 1 = 0)
    (d1Equation2 : values 41 = 0)
    (d2Equation0 : values 55 = 0)
    (d2Inverse1 : R)
    (d2Equation1 : values 56 * d2Inverse1 - 1 = 0)
    (d2Equation2 : values 57 = 0)
    : False := by
  exact nodeB422Impossible values rootZero d0Inverse0 d0Equation0 d0Equation1 d0Equation2 d1Equation0 d1Inverse1 d1Equation1 d1Equation2 d2Equation0 d2Inverse1 d2Equation1 d2Equation2

#print axioms Krenn.Component60.SelectedSubtreeB4_2_2.subtreeB4_2_2Impossible

end Krenn.Component60.SelectedSubtreeB4_2_2
