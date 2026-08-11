import Mettapedia.GraphTheory.FourColor.GoertzelV24BoundaryProfileFiniteState
import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorOpenProfile

/-!
# Finite boundary profiles for arbitrary edge regions

The corridor prefix used by compositional pumping is an edge region rather
than necessarily a vertex side.  Boundary-local face fragments and their
uniform finite bound depend only on the displayed cut-edge set, so the
existing boundary-fragment construction applies without manufacturing a
vertex-side predicate.

This file packages an arbitrary finite region and an ordered list of crossing
edges as graph-derived cut data.  Its bounded regional profile is computed
from an open-region color function; no ambient closed coloring is required.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RegionalBoundaryProfileFiniteState

open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The finite cut displayed by an ordered crossing-edge coordinate. -/
def indexedCrossingEdgeSet {crossingEdgeCount : Nat}
    (crossingEdge : Fin crossingEdgeCount → E) : Finset E :=
  Finset.univ.image crossingEdge

omit [Fintype E] in
@[simp]
theorem mem_indexedCrossingEdgeSet_iff {crossingEdgeCount : Nat}
    (crossingEdge : Fin crossingEdgeCount → E) (edge : E) :
    edge ∈ indexedCrossingEdgeSet crossingEdge ↔
      ∃ index, crossingEdge index = edge := by
  simp [indexedCrossingEdgeSet]

omit [Fintype E] in
/-- Repeated crossing coordinates can only decrease the cardinality of the
displayed cut. -/
theorem card_indexedCrossingEdgeSet_le {crossingEdgeCount : Nat}
    (crossingEdge : Fin crossingEdgeCount → E) :
    (indexedCrossingEdgeSet crossingEdge).card ≤ crossingEdgeCount := by
  calc
    (indexedCrossingEdgeSet crossingEdge).card ≤
        (Finset.univ : Finset (Fin crossingEdgeCount)).card := by
      exact Finset.card_image_le
    _ = crossingEdgeCount := by simp

omit [Fintype E] in
/-- An injective ordered coordinate enumerates its displayed cut exactly. -/
theorem card_indexedCrossingEdgeSet_eq {crossingEdgeCount : Nat}
    (crossingEdge : Fin crossingEdgeCount → E)
    (hinjective : Function.Injective crossingEdge) :
    (indexedCrossingEdgeSet crossingEdge).card = crossingEdgeCount := by
  rw [indexedCrossingEdgeSet,
    Finset.card_image_iff.mpr hinjective.injOn]
  simp

/-- Boundary-local graph-derived data for an arbitrary edge region and a
caller-supplied crossing order.  Only fragments that meet the displayed cut
survive in the profile carrier. -/
def regionalBoundaryGraphCutData
    (RS : RotationSystem V E) (region : Finset E)
    {crossingEdgeCount : Nat} (crossingEdge : Fin crossingEdgeCount → E) :
    GraphCorridorCutData RS crossingEdgeCount 0
      (Fintype.card (BoundaryRegionalFragment RS
        (indexedCrossingEdgeSet crossingEdge) region)) where
  regionEdges := region
  crossingEdge := crossingEdge
  terminalEdge := fun terminal => Fin.elim0 terminal
  fragmentFace := fun fragment =>
    (boundaryRegionalFragmentAt RS
      (indexedCrossingEdgeSet crossingEdge) region fragment).1.1
  fragmentEdges := fun fragment =>
    boundaryRegionalFragmentEdges RS
      (indexedCrossingEdgeSet crossingEdge) region
      (boundaryRegionalFragmentAt RS
        (indexedCrossingEdgeSet crossingEdge) region fragment)

/-- If the displayed crossing edges lie in the region, every port of the
arbitrary-region cut data is a genuine regional edge. -/
theorem regionalBoundaryGraphCutData_portsInRegion
    (RS : RotationSystem V E) (region : Finset E)
    {crossingEdgeCount : Nat} (crossingEdge : Fin crossingEdgeCount → E)
    (hcrossing : ∀ index, crossingEdge index ∈ region) :
    (regionalBoundaryGraphCutData RS region crossingEdge).PortsInRegion := by
  intro port
  rcases port with crossing | terminal
  · exact hcrossing crossing
  · exact Fin.elim0 terminal

/-- An injective crossing order gives pairwise distinct ports. -/
theorem regionalBoundaryGraphCutData_portsInjective
    (RS : RotationSystem V E) (region : Finset E)
    {crossingEdgeCount : Nat} (crossingEdge : Fin crossingEdgeCount → E)
    (hinjective : Function.Injective crossingEdge) :
    (regionalBoundaryGraphCutData RS region crossingEdge).PortsInjective := by
  intro first second heq
  rcases first with first | first
  · rcases second with second | second
    · congr 1
      exact hinjective heq
    · exact Fin.elim0 second
  · exact Fin.elim0 first

/-- The face-fragment fields are valid by their occurrence-sensitive
connected-component construction. -/
theorem regionalBoundaryGraphCutData_fragmentsOnFaceInRegion
    (RS : RotationSystem V E) (region : Finset E)
    {crossingEdgeCount : Nat} (crossingEdge : Fin crossingEdgeCount → E) :
    (regionalBoundaryGraphCutData RS region crossingEdge).FragmentsOnFaceInRegion := by
  intro fragment
  exact boundaryRegionalFragmentEdges_subset_boundary_inter_region RS
    (indexedCrossingEdgeSet crossingEdge) region
    (boundaryRegionalFragmentAt RS
      (indexedCrossingEdgeSet crossingEdge) region fragment)

/-- The number of boundary-local face fragments is controlled solely by the
number of displayed crossing coordinates, even when a face traverses a bridge
edge twice. -/
theorem regionalBoundaryGraphCutData_fragmentCount_le_two_mul
    (RS : RotationSystem V E) (region : Finset E)
    {crossingEdgeCount : Nat} (crossingEdge : Fin crossingEdgeCount → E) :
    Fintype.card (BoundaryRegionalFragment RS
      (indexedCrossingEdgeSet crossingEdge) region) ≤
        2 * crossingEdgeCount := by
  calc
    Fintype.card (BoundaryRegionalFragment RS
        (indexedCrossingEdgeSet crossingEdge) region) ≤
        2 * (indexedCrossingEdgeSet crossingEdge).card :=
      card_boundaryRegionalFragment_le_two_mul_card_of_dartOccurrences RS
        (indexedCrossingEdgeSet crossingEdge) region
    _ ≤ 2 * crossingEdgeCount :=
      Nat.mul_le_mul_left 2 (card_indexedCrossingEdgeSet_le crossingEdge)

/-- The complete open-region profile in the common finite carrier.  Its
coordinates are the actual cut colors, tracked connectivity, face
continuation, port incidence, and capped face progress of `region`. -/
def regionalBoundaryBoundedProfile
    (RS : RotationSystem V E) (region : Finset E)
    {crossingEdgeCount : Nat} (crossingEdge : Fin crossingEdgeCount → E)
    (color : E → Color)
    (hcolor : ∀ index, color (crossingEdge index) ≠ 0) :
    BoundedCorridorCutProfile crossingEdgeCount 0
      (2 * crossingEdgeCount) where
  faceFragmentCount :=
    ⟨Fintype.card (BoundaryRegionalFragment RS
        (indexedCrossingEdgeSet crossingEdge) region),
      Nat.lt_succ_of_le
        (regionalBoundaryGraphCutData_fragmentCount_le_two_mul
          RS region crossingEdge)⟩
  profile :=
    (regionalBoundaryGraphCutData RS region crossingEdge).regionalProfile
      color hcolor

end

end GoertzelV24RegionalBoundaryProfileFiniteState

end Mettapedia.GraphTheory.FourColor
