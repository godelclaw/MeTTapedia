import MettapediaFourColor.WheelBoundaryCompletion
import MettapediaFourColor.D3009Boundary

/-!
# The original wheel consumes shared boundary completion

The thirteen-port source supplies the same finite row and owner laws used
by the broader wheel family. This adapter retains its existing source labels.
-/

namespace FourColor.D3009BoundaryLayout

open D3009Wheel

/-- The original thirteen-port source consumes the general completion law. -/
def layout : WheelBoundaryCompletion.Layout 13 where
  graph := D3009Wheel.input.graph
  degree := D3009Wheel.degree
  degree_pos := D3009Boundary.degree_pos
  star_le := fun i => (star_specs i).2.1
  fullSpoke := D3009Boundary.fullSpoke
  fullSpoke_core := D3009Boundary.fullSpoke_core
  owner := D3009Boundary.owner
  owner_bounds := D3009Boundary.owner_bounds
  ring_cases := D3009Boundary.ring_cases
  edge_reading := D3009Boundary.edge_reading
  owner_strict := D3009Boundary.owner_strict
  owner_injective := D3009Boundary.owner_injective
  owner_neighbors := D3009Boundary.owner_neighbors
  center_core := D3009Boundary.center_core

end FourColor.D3009BoundaryLayout
