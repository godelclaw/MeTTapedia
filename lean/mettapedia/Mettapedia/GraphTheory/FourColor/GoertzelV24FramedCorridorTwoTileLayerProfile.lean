import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorTwoTileLayerBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebProfileSpliceBridge

/-!
# Ordered finite profiles of concrete two-tile source layers

A two-tile source layer is now a retained simple facial-dual cycle with an
exact graph-side boundary.  This file gives that boundary the finite profile
used by the pumping argument, retaining the order in which its six primal
ports are crossed.  The coordinate is therefore supplied by the actual
source layer walk, not by an arbitrary finite enumeration.

The chosen deletion component is only a certified side of this individual
layer.  Establishing which two distant layers bound the pumpable annulus is a
separate corridor-assembly obligation; nothing here treats a local cycle as
that global annulus.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24CleanHexCorridor
open GoertzelV24ClosedWebProfileFiniteness
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationVertexCutProfile
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance twoTileLayerProfileGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceCornerAlignedTwoTileLayerBoundary

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}
  {hnextNext :
    (nextCorridorInterior leftInterior hnext).center.val + 2 < blockLength}
  {first : SourceCornerAlignedSlabInterface realization htwoSided hunique
    leftInterior hnext}
  {second : SourceCornerAlignedSlabInterface realization htwoSided hunique
    (nextCorridorInterior leftInterior hnext) hnextNext}

/-- A retained graph-side component of the concrete six-edge source layer. -/
noncomputable def component
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    (G.deleteEdges (edgeFinsetValueSet boundary.cutEdges)).ConnectedComponent :=
  Classical.choose boundary.exists_component_exactBoundary

/-- The selected component has exactly the primal wall crossed by the
source's simple two-tile layer. -/
theorem component_boundary
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    componentCrossingEdges boundary.cutEdges boundary.component = boundary.cutEdges := by
  exact Classical.choose_spec boundary.exists_component_exactBoundary

/-- The finite vertex side carried by the selected deletion component. -/
noncomputable def componentSide
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) : Finset V := by
  classical
  exact Finset.univ.filter fun vertex => vertex ∈ boundary.component.supp

@[simp]
theorem mem_componentSide_iff
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second)
    (vertex : V) :
    vertex ∈ boundary.componentSide ↔ vertex ∈ boundary.component.supp := by
  classical
  simp [componentSide]

/-- The computed rotation-system cut is exactly the six primal edges crossed
by the retained source layer. -/
theorem vertexSetCrossingEdges_componentSide_eq_cutEdges
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
      boundary.componentSide = boundary.cutEdges := by
  ext edge
  calc
    edge ∈ vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        boundary.componentSide ↔
        EdgeCrossesVertexSide G
          (fun vertex => vertex ∈ boundary.componentSide) edge := by
          exact mem_simpleGraph_vertexSetCrossingEdges_iff
            embedded.cellulation.rotation boundary.componentSide edge
    _ ↔ EdgeCrossesVertexSide G
          (fun vertex => vertex ∈ boundary.component.supp) edge := by
          simp only [mem_componentSide_iff]
    _ ↔ edge ∈ componentCrossingEdges boundary.cutEdges boundary.component := by
          exact (mem_componentCrossingEdges_iff
            boundary.cutEdges boundary.component edge).symm
    _ ↔ edge ∈ boundary.cutEdges := by rw [boundary.component_boundary]

/-- The concrete two-tile layer has precisely six graph-profile ports. -/
theorem crossingCard_eq_six
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem boundary.componentSide) = 6 := by
  rw [card_vertexSetCrossingEdge,
    boundary.vertexSetCrossingEdges_componentSide_eq_cutEdges,
    boundary.cutEdges_card_eq_six]

/-- The primal crossing at a literal position of the six-step source layer. -/
noncomputable def orderedCrossing
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second)
    (step : Fin 6) : G.edgeSet :=
  dualWalkCrossingEdge
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    boundary.walk
    (Fin.cast boundary.length_eq_six.symm step)

/-- Each literal source-layer crossing is a real port of its deletion side. -/
theorem orderedCrossing_mem
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second)
    (step : Fin 6) :
    boundary.orderedCrossing step ∈
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        boundary.componentSide := by
  rw [boundary.vertexSetCrossingEdges_componentSide_eq_cutEdges, cutEdges]
  exact (mem_dualWalkCrossingEdges_iff
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    boundary.walk _).2
      ⟨Fin.cast boundary.length_eq_six.symm step, rfl⟩

/-- Traversing the simple source layer never repeats a primal crossing edge. -/
theorem orderedCrossing_injective
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    Function.Injective boundary.orderedCrossing := by
  intro left right heq
  apply Fin.cast_injective boundary.length_eq_six.symm
  apply dualWalkCrossingEdge_injective_of_isCycle
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))
    (orbitFace_incidence_le_two embedded.cellulation.rotation.toRotationSystem)
    hunique boundary.walk boundary.isCycle
  simpa [orderedCrossing] using heq

/-- The literal six-step order covers every crossing port of the constructed
vertex side. -/
theorem exists_orderedCrossing_eq
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second)
    (edge : G.edgeSet)
    (hedge : edge ∈
      vertexSetCrossingEdges embedded.cellulation.rotation.toRotationSystem
        boundary.componentSide) :
    ∃ step : Fin 6, boundary.orderedCrossing step = edge := by
  have hcut : edge ∈ boundary.cutEdges := by
    rw [← boundary.vertexSetCrossingEdges_componentSide_eq_cutEdges]
    exact hedge
  rw [cutEdges] at hcut
  rcases (mem_dualWalkCrossingEdges_iff
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
    boundary.walk edge).1 hcut with ⟨walkStep, hwalkStep⟩
  let step : Fin 6 := Fin.cast boundary.length_eq_six walkStep
  refine ⟨step, ?_⟩
  change dualWalkCrossingEdge
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)) hunique
      boundary.walk
      (Fin.cast boundary.length_eq_six.symm step) = edge
  have hcast : Fin.cast boundary.length_eq_six.symm step = walkStep := by
    apply Fin.ext
    rfl
  rw [hcast]
  exact hwalkStep

/-- The actual source-layer walk gives the exact indexing used by the finite
profile engine; it is a geometric coordinate, not `Fintype.equivFin`. -/
noncomputable def crossingIndexing
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :
    VertexSetCrossingIndexing embedded.cellulation.rotation.toRotationSystem
      boundary.componentSide := by
  let hcard : Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem boundary.componentSide) = 6 :=
    boundary.crossingCard_eq_six
  apply Equiv.ofBijective
    (fun index =>
      ⟨boundary.orderedCrossing (Fin.cast hcard index),
        boundary.orderedCrossing_mem (Fin.cast hcard index)⟩)
  constructor
  · intro left right hports
    apply Fin.cast_injective hcard
    apply boundary.orderedCrossing_injective
    exact congrArg Subtype.val hports
  · intro port
    rcases boundary.exists_orderedCrossing_eq port.1 port.2 with ⟨step, hstep⟩
    let sourceStep : Fin (Fintype.card (VertexSetCrossingEdge
        embedded.cellulation.rotation.toRotationSystem boundary.componentSide)) :=
      Fin.cast hcard.symm step
    refine ⟨sourceStep, ?_⟩
    apply Subtype.ext
    change boundary.orderedCrossing (Fin.cast hcard sourceStep) = port.1
    have hcast : Fin.cast hcard sourceStep = step := by
      apply Fin.ext
      rfl
    rw [hcast]
    exact hstep

/-- The full finite profile data of a concrete two-tile source layer, with
the six ports ordered by the source's own facial-dual walk. -/
noncomputable def orderedProfileData
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second) :=
  vertexSetBoundaryGraphCutDataWithIndexing
    embedded.cellulation.rotation.toRotationSystem boundary.componentSide
    boundary.crossingIndexing

/-- Reading profile coordinates recovers the literal source-layer crossings,
up to the harmless proof transport from its cardinality to `Fin 6`. -/
theorem orderedProfileData_crossingEdge
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second)
    (index : Fin (Fintype.card (VertexSetCrossingEdge
      embedded.cellulation.rotation.toRotationSystem boundary.componentSide))) :
    boundary.orderedProfileData.crossingEdge index =
      boundary.orderedCrossing (Fin.cast boundary.crossingCard_eq_six index) := by
  rfl

/-- Put the concrete two-tile source layer into the manuscript's finite
profile carrier.  The bound is six because all six crossings of the simple
layer are retained, including the two joining the adjacent source tiles. -/
noncomputable def orderedDepthProfile
    (boundary : SourceCornerAlignedTwoTileLayerBoundary first second)
    (coloring : embedded.cellulation.rotation.toRotationSystem.EdgeColoring Color)
    (hcoloring : embedded.cellulation.rotation.toRotationSystem.IsTaitEdgeColoring
      coloring) :
    ClosedWebDepthProfile 6 :=
  GoertzelV24ClosedWebProfileSpliceBridge.graphCutDepthProfile 6
    boundary.orderedProfileData coloring hcoloring
    (by rw [boundary.crossingCard_eq_six])
    (vertexSetBoundaryGraphCutData_fragmentCount_le_two_mul_crossingPortCount_of_dartOccurrences
      embedded.cellulation.rotation.toRotationSystem boundary.componentSide)

end SourceCornerAlignedTwoTileLayerBoundary

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
