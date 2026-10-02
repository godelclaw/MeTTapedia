import MettapediaFourColor.TwoFiveWheelData

/-!
# One repair contract supplies all six two-five wheels

The thirteen-port wheel is obtained by the same boundary-triangle subdivision
at each of six rim positions. Joint boundary repair descends through that
operation. No separate colouring or Kempe certificate is used for a target.
The full repair of the source remains an explicit hypothesis.
-/

namespace FourColor.TwoFiveWheelRepair

open KempeBoundarySplit TwoFiveWheelData
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

/-- Changing any one of the six rim degrees from six to five reuses the same
source repair, retaining the two inserted edge colours jointly. -/
theorem transfer (base : Repairs
    (GraphTrace D3009Wheel.input.graph D3009Wheel.input.boundary) 13) (p : Fin 6) :
    Repairs (GraphTrace (input p).graph (input p).boundary) 12 := by
  have split : Repairs (GraphTrace
      (subdivide (input p).graph (left p) (right p) (apex p))
      (BoundaryTriangleRepair.ports (left p) (right p) (tail p))) 13 :=
    BoundaryRepairTransport.repairs (insertion p) _ D3009Wheel.input.boundary
      (14 - (cut p).val) (source_boundary p) base
  have collapsed := BoundaryTriangleRepair.repair (input p).graph
    (left p) (right p) (apex p) (tail p)
    (by simpa only [tail_length] using split)
  have result := BoundaryRepairTransport.repairs
    (SimpleGraph.Iso.refl (G := (input p).graph)) (input p).boundary
    (left p :: right p :: tail p) ((cut p).val - 1)
    (by
      change (((input p).boundary.map id).rotate ((cut p).val - 1)) = _
      simpa only [List.map_id] using base_boundary p) collapsed
  simpa only [tail_length] using result

/-- Reconstruction returns an actual colouring compatible with the same
Kempe-closed joint exterior relation. -/
theorem reconstruct (base : Repairs
    (GraphTrace D3009Wheel.input.graph D3009Wheel.input.boundary) 13) (p : Fin 6)
    (et : List Color) (length : et.length = 12) (proper : (0 : Color) ∉ et)
    (conserved : et.sum = 0) (Q : List Color → Prop) (closed : KempeClosed Q)
    (outside : Q et) :
    ∃ k : (input p).graph.Coloring Color, Q (trace ((input p).boundary.map k)) := by
  obtain ⟨es, ⟨k, rfl⟩, compatible⟩ :=
    transfer base p et length proper conserved Q closed outside
  exact ⟨k, compatible⟩

end FourColor.TwoFiveWheelRepair
