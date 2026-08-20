import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailMiddleReplacementCycles
import Mettapedia.GraphTheory.FourColor.GoertzelV24SelectedDualCycleSeparator

/-!
# The middle-replacement short cycles are literal primal separators

The fail-closed middle rail replacement exposes a simple interior facial-dual
cycle of length three or four whenever neither centre case occurs.  This module
selects one actual primal crossing at every dual step and applies the generic
selected-cycle separator theorem.  The resulting primal cut has cardinality
three or four, avoids both named hole boundaries, and disconnects the graph
underlying the framed annular cellulation.

This is positive separator data for the source rotor/square consumer.  It does
not apply either reduction, eliminate the two centre cases, construct the
rolling transition, attach end caps, or close the separated-crosscut
obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24SelectedDualCycleSeparator

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}

namespace MiddleReplacementShortDualCycle

/-- Select one actual primal edge crossed by each step of the short dual
cycle.  No global face-intersection uniqueness is required. -/
noncomputable def selectedCycle
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    SelectedDualCycle web.annular.RS cycle.start :=
  SelectedDualCycle.ofWalkWithCrossingAt web.annular.RS cycle.walk cycle.isCycle
    cycle.anchor cycle.anchorEdge cycle.anchorEdge_mem_shared

@[simp] theorem selectedCycle_walk
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    cycle.selectedCycle.walk = cycle.walk := rfl

/-- The selected separator retains the literal source rung recorded by the
short-cycle construction. -/
@[simp] theorem selectedCycle_crossingEdge_anchor
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    cycle.selectedCycle.crossingEdge cycle.anchor = cycle.anchorEdge := by
  exact SelectedDualCycle.ofWalkWithCrossingAt_crossingEdge
    web.annular.RS cycle.walk cycle.isCycle cycle.anchor cycle.anchorEdge
      cycle.anchorEdge_mem_shared

/-- The selected primal cut has the same cardinality as the short dual
cycle. -/
theorem crossingEdges_card_eq_length
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    cycle.selectedCycle.crossingEdges.card = cycle.walk.length := by
  exact cycle.selectedCycle.card_crossingEdges_eq_length
    (orbitFace_incidence_le_two web.annular.RS)

/-- Hence the selected primal cut has exactly three or four edges. -/
theorem crossingEdges_card_eq_three_or_four
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    cycle.selectedCycle.crossingEdges.card = 3 ∨
      cycle.selectedCycle.crossingEdges.card = 4 := by
  rw [cycle.crossingEdges_card_eq_length]
  exact cycle.length_eq_three_or_four

/-- The selected separator avoids the designated inner-hole boundary. -/
theorem crossingEdges_disjoint_innerHoleBoundary
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    Disjoint cycle.selectedCycle.crossingEdges
      (orbitFaceBoundary web.annular.RS
        web.annular.cellulation.innerHole) := by
  exact cycle.selectedCycle.crossingEdges_disjoint_faceBoundary_of_support
    web.annular.cellulation.interiorFaces cycle.support_internal
    web.annular.cellulation.innerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

/-- The selected separator also avoids the designated outer-hole boundary. -/
theorem crossingEdges_disjoint_outerHoleBoundary
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    Disjoint cycle.selectedCycle.crossingEdges
      (orbitFaceBoundary web.annular.RS
        web.annular.cellulation.outerHole) := by
  exact cycle.selectedCycle.crossingEdges_disjoint_faceBoundary_of_support
    web.annular.cellulation.interiorFaces cycle.support_internal
    web.annular.cellulation.outerHole
    (by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces])

/-- Deleting the three or four selected primal crossings disconnects the
graph underlying the literal framed annulus. -/
theorem not_connected_deleteEdges_primalCut
    {face : AmbientFace
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    (cycle : MiddleReplacementShortDualCycle (web := web) face) :
    ¬ (G.deleteEdges cycle.selectedCycle.primalCut).Connected := by
  exact cycle.selectedCycle.not_connected_deleteEdges_primalCut
    web.annular.cellulation.rotation
    web.annular.cellulation.fullOrbitFaceInteriorDual_connected
    web.annular.cellulation.connected
    web.annular.cellulation.euler

end MiddleReplacementShortDualCycle

end Instance.SelectedLocalLayerFormation.SelectedSourceLocalRailAssembly

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
