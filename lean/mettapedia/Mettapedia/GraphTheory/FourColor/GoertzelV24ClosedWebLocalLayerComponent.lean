import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerFormation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedLocalDualCycleBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedLocalDualCycleSeparator

/-!
# Exact deletion component of a Cell-3 corridor layer

The two source-derived local layers in a boundary-clean Cell-3 corridor form
a simple facial-dual loop. This file turns that literal loop into an exact
primal deletion component. Crucially, the proof invokes two-sidedness only
for faces on the layer loop, whose annular-interior status is already part of
the source corridor construction; the named degree-one hole stubs remain
outside this local hypothesis.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24AnnularCrosscut
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualPathTransversal
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24FramedLocalDualCycleBond
open GoertzelV24FramedLocalDualCycleSeparator
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerComponentEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerPair

/-- A layer face is annular-interior, so its certified simple boundary keeps
the two darts of every incident edge on distinct face orbits.  This is proved
locally from the Cell-3 geometry; it does not assert global two-sidedness of
the open tangle's named hole faces. -/
private theorem dartOrbitFace_ne_alpha_of_mem_interiorFaces
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    (web : Instance data coloring) (dart : web.annular.RS.D)
    (hface : dartOrbitFace web.annular.RS dart ∈
      web.annular.cellulation.interiorFaces) :
    dartOrbitFace web.annular.RS dart ≠
      dartOrbitFace web.annular.RS (web.annular.RS.alpha dart) := by
  intro hsame
  have hsimple :
      (orbitFaceBoundary web.annular.RS
        (dartOrbitFace web.annular.RS dart)).card =
        (orbitFaceDarts web.annular.RS
          (dartOrbitFace web.annular.RS dart)).card := by
    simpa [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.faceLength]
      using web.geometry.internalBoundarySimple
        (dartOrbitFace web.annular.RS dart) hface
  have hinjective : Set.InjOn web.annular.RS.edgeOf
      (orbitFaceDarts web.annular.RS
        (dartOrbitFace web.annular.RS dart)) := by
    apply Finset.card_image_iff.mp
    exact hsimple
  have hdart : dart ∈ orbitFaceDarts web.annular.RS
      (dartOrbitFace web.annular.RS dart) :=
    (mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS dart) dart).2 rfl
  have halpha : web.annular.RS.alpha dart ∈ orbitFaceDarts web.annular.RS
      (dartOrbitFace web.annular.RS dart) :=
    (mem_orbitFaceDarts_iff web.annular.RS
      (dartOrbitFace web.annular.RS dart)
      (web.annular.RS.alpha dart)).2 hsame.symm
  have heq := hinjective hdart halpha
    (web.annular.RS.edge_alpha dart).symm
  exact web.annular.RS.alpha_fixfree dart heq.symm

/-- The finite primal wall crossed by the simple dual loop of a source-local
Cell-3 layer pair. -/
noncomputable def cutEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
    (layers.separatedLocalLayerPair hunique).dualLoop

/-- The literal two-tile Cell-3 layer boundary crosses exactly four distinct
primal edges.  This is the finite collar around the local rung pair: it is
read from the constructed facial-dual loop, rather than supplied as an
abstract four-edge cut. -/
theorem cutEdges_card_eq_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    (layers.cutEdges hunique).card = 4 := by
  change (dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
    layers.localLayerLoop).card = 4
  rw [card_dualWalkCrossingEdges_eq_length_of_isCycle_core
    (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS))
    (orbitFace_incidence_le_two web.annular.RS) hunique
    layers.localLayerLoop
    (layers.separatedLocalLayerPair_dualLoop_isCycle hunique)]
  simp [localLayerLoop, firstWalk, secondWalk]

end LocalLayerPair

namespace LocalLayerFormation

/-- The deletion-facing cut of a source-local Cell-3 layer is the literal
four-edge collar read from its two flanking source slots.  This connects the
generic component API to the concrete source witness without treating the
local collar as a completed global transversal. -/
theorem SourceLocalLayerPairWitness.cutEdges_eq_sourceCorners
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (witness : SourceLocalLayerPairWitness web corridor hunique leftInterior hnext) :
    witness.toLocalLayerPair.cutEdges hunique =
      {web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS witness.placement.root witness.before.1),
        web.annular.RS.edgeOf
          (faceCycleDart web.annular.RS witness.placement.root witness.after.1)} ∪
      {web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.before.1))),
        web.annular.RS.edgeOf
          (web.annular.RS.rho (web.annular.RS.phi
            (faceCycleDart web.annular.RS witness.placement.root
              witness.placement.outgoingPosition)))} := by
  change dualWalkCrossingEdges (orbitFaceBoundary web.annular.RS)
    (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique
    witness.toLocalLayerPair.localLayerLoop = _
  exact witness.localLayerLoop_crossingEdges_eq_sourceCorners

end LocalLayerFormation

namespace LocalLayerPair

omit [DecidableEq V] in
/-- A nontrivial finite edge deletion in a connected graph has a nonempty
original-graph boundary whenever another deletion component exists. -/
private theorem componentCrossingEdges_nonempty_of_distinct
    (hconnected : G.Connected) (removed : Finset G.edgeSet)
    (inside outside :
      (G.deleteEdges (localEdgeFinsetValueSet removed)).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    (localComponentCrossingEdges removed inside).Nonempty := by
  rcases inside.nonempty_supp with ⟨insideVertex, hinside⟩
  rcases outside.nonempty_supp with ⟨outsideVertex, houtside⟩
  have houtsideNotInside : outsideVertex ∉ inside.supp := by
    intro hcommon
    apply hdistinct
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hcommon houtside
  rcases hconnected insideVertex outsideVertex with ⟨walk⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      (fun vertex => vertex ∈ inside.supp) walk hinside houtsideNotInside with
    ⟨edge, _hwalkEdge, hcross⟩
  exact ⟨edge,
    (mem_localComponentCrossingEdges_iff removed inside edge).2 hcross⟩

/-- A Cell-3 local layer supplies a genuine finite deletion component whose
computed graph boundary is exactly its crossed primal wall. This is the
component/removed/boundary part of the source splice geometry, constructed
without treating the open tangle's hole stubs as two-sided. -/
theorem exists_component_exactBoundary
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    ∃ component : (G.deleteEdges
        (localEdgeFinsetValueSet (layers.cutEdges hunique))).ConnectedComponent,
      localComponentCrossingEdges (layers.cutEdges hunique) component =
        layers.cutEdges hunique := by
  have hcut :
      localDualWalkPrimalCut web.annular.cellulation.rotation hunique
        (layers.separatedLocalLayerPair hunique).dualLoop =
        localEdgeFinsetValueSet (layers.cutEdges hunique) := by
    exact localDualWalkPrimalCut_eq_localEdgeFinsetValueSet_dualWalkCrossingEdges
      web.annular.cellulation.rotation hunique
      (layers.separatedLocalLayerPair hunique).dualLoop
  have hnotConnected : ¬ (G.deleteEdges
      (localEdgeFinsetValueSet (layers.cutEdges hunique))).Connected := by
    rw [← hcut]
    exact not_connected_deleteEdges_localDualWalkPrimalCut_of_isCycle
      web.annular.cellulation.rotation
      (GoertzelV24AnnularCrosscut.holeDual_connected web.annular)
      web.annular.cellulation.connected web.annular.cellulation.euler hunique
      (layers.separatedLocalLayerPair hunique).dualLoop
      (layers.separatedLocalLayerPair_dualLoop_isCycle hunique)
  rcases exists_distinct_localComponents_of_not_connected
      web.annular.cellulation.connected (layers.cutEdges hunique) hnotConnected with
    ⟨inside, outside, hdistinct⟩
  refine ⟨inside, ?_⟩
  have hcomponentBoundary : localComponentCrossingEdges
      (layers.cutEdges hunique) inside =
      localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) := by
    ext edge
    simp [localComponentCrossingEdges, localCrossingEdgeFinset]
  have hsubset : localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) ⊆
      layers.cutEdges hunique := by
    rw [← hcomponentBoundary]
    exact localComponentCrossingEdges_subset_removed (layers.cutEdges hunique)
      inside
  have hnonempty :
      (localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp)).Nonempty := by
    rw [← hcomponentBoundary]
    exact componentCrossingEdges_nonempty_of_distinct
      web.annular.cellulation.connected (layers.cutEdges hunique)
      inside outside hdistinct
  have hboundary : localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) =
      layers.cutEdges hunique := by
    apply crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset_of_supportTwoSided
      web.annular.cellulation.rotation hunique
      (layers.separatedLocalLayerPair hunique).dualLoop
      (layers.separatedLocalLayerPair_dualLoop_isCycle hunique)
      (fun vertex => vertex ∈ inside.supp) hsubset hnonempty
    intro face hface dart hdart
    apply dartOrbitFace_ne_alpha_of_mem_interiorFaces web dart
    rw [hdart]
    exact layers.separatedLocalLayerPair_dualLoop_support_internal
      hunique face hface
  rw [hcomponentBoundary]
  exact hboundary

/-- The source-local Cell-3 layer is a genuine separator: deleting precisely
its crossed primal edges disconnects the ambient graph.  This exposes the
separation fact separately from the choice of a retained component, so later
splice formation can choose the side containing a named source boundary. -/
theorem not_connected_delete_cutEdges
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    ¬ (G.deleteEdges
      (localEdgeFinsetValueSet (layers.cutEdges hunique))).Connected := by
  have hcut :
      localDualWalkPrimalCut web.annular.cellulation.rotation hunique
        (layers.separatedLocalLayerPair hunique).dualLoop =
        localEdgeFinsetValueSet (layers.cutEdges hunique) := by
    exact localDualWalkPrimalCut_eq_localEdgeFinsetValueSet_dualWalkCrossingEdges
      web.annular.cellulation.rotation hunique
      (layers.separatedLocalLayerPair hunique).dualLoop
  rw [← hcut]
  exact not_connected_deleteEdges_localDualWalkPrimalCut_of_isCycle
    web.annular.cellulation.rotation
    (GoertzelV24AnnularCrosscut.holeDual_connected web.annular)
    web.annular.cellulation.connected web.annular.cellulation.euler hunique
    (layers.separatedLocalLayerPair hunique).dualLoop
    (layers.separatedLocalLayerPair_dualLoop_isCycle hunique)

/-- Any one of two distinct deletion components sees the entire local Cell-3
wall as its computed boundary.  The proof uses only the two-sidedness of
faces on the literal layer loop, not a global two-sidedness assertion about
the open tangle's hole faces. -/
theorem componentCrossingEdges_eq_cutEdges_of_distinct
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (inside outside :
      (G.deleteEdges (localEdgeFinsetValueSet
        (layers.cutEdges hunique))).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    localComponentCrossingEdges (layers.cutEdges hunique) inside =
      layers.cutEdges hunique := by
  have hcomponentBoundary : localComponentCrossingEdges
      (layers.cutEdges hunique) inside =
      localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) := by
    ext edge
    simp [localComponentCrossingEdges, localCrossingEdgeFinset]
  have hsubset : localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) ⊆
      layers.cutEdges hunique := by
    rw [← hcomponentBoundary]
    exact localComponentCrossingEdges_subset_removed (layers.cutEdges hunique)
      inside
  have hnonempty :
      (localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp)).Nonempty := by
    rw [← hcomponentBoundary]
    exact componentCrossingEdges_nonempty_of_distinct
      web.annular.cellulation.connected (layers.cutEdges hunique)
      inside outside hdistinct
  have hboundary : localCrossingEdgeFinset G (fun vertex => vertex ∈ inside.supp) =
      layers.cutEdges hunique := by
    apply crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset_of_supportTwoSided
      web.annular.cellulation.rotation hunique
      (layers.separatedLocalLayerPair hunique).dualLoop
      (layers.separatedLocalLayerPair_dualLoop_isCycle hunique)
      (fun vertex => vertex ∈ inside.supp) hsubset hnonempty
    intro face hface dart hdart
    apply dartOrbitFace_ne_alpha_of_mem_interiorFaces web dart
    rw [hdart]
    exact layers.separatedLocalLayerPair_dualLoop_support_internal
      hunique face hface
  rw [hcomponentBoundary]
  exact hboundary

/-- Select the literal deletion component containing the source's designated
outer dart.  The other component supplies a real removed vertex.  This is
the outer-retained half of the Cell-3 splice checklist; preservation of the
inner hole is a later global-layer obligation, not silently assumed here. -/
theorem exists_outer_component_exactBoundary_and_removed
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    (layers : LocalLayerPair web corridor leftInterior hnext)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))) :
    ∃ component : (G.deleteEdges
        (localEdgeFinsetValueSet (layers.cutEdges hunique))).ConnectedComponent,
      ∃ removed : V,
        web.annular.RS.vertOf web.annular.RS.outer ∈ component.supp ∧
        removed ∉ component.supp ∧
        localComponentCrossingEdges (layers.cutEdges hunique) component =
          layers.cutEdges hunique := by
  let outerVertex := web.annular.RS.vertOf web.annular.RS.outer
  let outerComponent : (G.deleteEdges
      (localEdgeFinsetValueSet (layers.cutEdges hunique))).ConnectedComponent :=
    (G.deleteEdges (localEdgeFinsetValueSet
      (layers.cutEdges hunique))).connectedComponentMk outerVertex
  have houterMem : outerVertex ∈ outerComponent.supp := by
    dsimp [outerComponent]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  rcases exists_distinct_localComponents_of_not_connected
      web.annular.cellulation.connected (layers.cutEdges hunique)
      (layers.not_connected_delete_cutEdges hunique) with
    ⟨inside, outside, hdistinct⟩
  by_cases hinside : inside = outerComponent
  · have houterNeOutside : outerComponent ≠ outside := by
      intro heq
      exact hdistinct (hinside.trans heq)
    rcases outside.nonempty_supp with ⟨removed, hremoved⟩
    have hremovedNotOuter : removed ∉ outerComponent.supp := by
      intro houter
      have heq : outside = outerComponent :=
        SimpleGraph.ConnectedComponent.eq_of_common_vertex hremoved houter
      exact hdistinct (hinside.trans heq.symm)
    refine ⟨outerComponent, removed, ?_, hremovedNotOuter, ?_⟩
    · simpa [outerVertex] using houterMem
    · exact layers.componentCrossingEdges_eq_cutEdges_of_distinct hunique
        outerComponent outside houterNeOutside
  · have houterNeInside : outerComponent ≠ inside := by
      intro heq
      exact hinside (heq.symm)
    rcases inside.nonempty_supp with ⟨removed, hremoved⟩
    have hremovedNotOuter : removed ∉ outerComponent.supp := by
      intro houter
      have heq : inside = outerComponent :=
        SimpleGraph.ConnectedComponent.eq_of_common_vertex hremoved houter
      exact hinside heq
    refine ⟨outerComponent, removed, ?_, hremovedNotOuter, ?_⟩
    · simpa [outerVertex] using houterMem
    · exact layers.componentCrossingEdges_eq_cutEdges_of_distinct hunique
        outerComponent inside houterNeInside

end LocalLayerPair

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
