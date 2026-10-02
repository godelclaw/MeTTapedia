import MettapediaFourColor.D3009BoundaryLayout
import MettapediaFourColor.TwoFiveWheelData

/-!
# The one-five and two-five wheels share one geometric completion theorem

Each layout supplies the finite row and owner laws required by
`WheelBoundaryCompletion`. The two-five layouts delete one private outer
position, retaining the shared seam owners. No ambient injectivity is
assumed by a layout: the general theorem derives it from short-cycle laws.
-/

namespace FourColor.WheelBoundaryLayouts

open D3009Wheel

set_option maxRecDepth 32768

def degree (p : Fin 6) (i : Fin 8) : ℕ :=
  (NearLinearDiamondData.coreRow (TwoFiveWheelData.input p).source i.val).getD 1 0

theorem degree_pos : ∀ p i, 0 < degree p i := by decide +kernel

def shift (p : Fin 6) (i : Fin 8) : ℕ :=
  if i = rim (TwoFiveWheelData.selected p) then 1 else D3009Boundary.shift i

def fullSpoke (p : Fin 6) (i : Fin 8) (j : Fin (degree p i)) : Fin 20 :=
  (((TwoFiveWheelData.input p).internalStar (i.natAdd 12)).rotate (shift p i)).getD j.val 0

def owner (p : Fin 6) (q : Fin 12) : Fin 8 × ℕ :=
  D3009Boundary.owner ⟨if q.val < (TwoFiveWheelData.cut p).val then q.val else q.val + 1,
    by split <;> omega⟩

set_option maxHeartbeats 4000000 in
/-- The six placements differ only in their finite rows and one removed owner. -/
def twoFive (p : Fin 6) : WheelBoundaryCompletion.Layout 12 where
  graph := (TwoFiveWheelData.input p).graph
  degree := degree p
  degree_pos := degree_pos p
  star_le := by revert p; decide +kernel
  fullSpoke := fullSpoke p
  fullSpoke_core := by revert p; decide +kernel
  owner := owner p
  owner_bounds := by revert p; decide +kernel
  ring_cases := by revert p; decide +kernel
  edge_reading := by revert p; decide +kernel
  owner_strict := by revert p; decide +kernel
  owner_injective := by revert p; decide +kernel
  owner_neighbors := by revert p; decide +kernel
  center_core := by revert p; decide +kernel

theorem degrees : ∀ p i, (twoFive p).degree (rim i) =
    if i = 0 ∨ i = TwoFiveWheelData.selected p then 5 else 6 := by decide +kernel

theorem center_degree : ∀ p, (twoFive p).degree 0 = 7 := by decide +kernel

end FourColor.WheelBoundaryLayouts
