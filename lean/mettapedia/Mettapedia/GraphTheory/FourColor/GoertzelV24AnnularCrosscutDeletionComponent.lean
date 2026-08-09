import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversalAppend
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutComponent
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutBond

/-!
# Deletion components of an annular crosscut separator

The paired source transversals form a simple dual loop.  This file turns its
finite list of crossed primal edges into actual connected components after
deletion.  Thus the retained side for the compositional splice is constructed
from the graph, rather than carried as an unproved geometric parameter.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24CubicSmallBoundaryCycle
open GoertzelV24DualCycleSeparator
open GoertzelV24DualCycleBond
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FiniteEdgeDeletion
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/- Reuse the separator's edge equality instance verbatim: finite edge lists
carry that instance in their elaborated terms, so changing it here would make
otherwise identical cut carriers fail to unify definitionally. -/
attribute [local instance] graphEdgeSetDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The finite edge carrier of the primal separator induced by the paired
annular crosscuts. -/
def primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    Finset G.edgeSet :=
  dualWalkCrossingEdges
    (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique pair.dualLoop

/-- The finite separator of the closed dual loop is exactly the disjoint
union of the two source transversal supports.  This is the bookkeeping
bridge from the loop used for separation back to the individual interfaces
used by the source splice. -/
theorem primalCutEdges_eq_sourceCrossingSupport
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    pair.primalCutEdges data =
      pair.left.crossingEdges hunique ∪ pair.right.crossingEdges hunique := by
  change dualWalkCrossingEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
        (pair.left.walk.append pair.right.walk.reverse) =
      dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
          pair.left.walk ∪
        dualWalkCrossingEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique
            pair.right.walk
  rw [dualWalkCrossingEdges_append,
    dualWalkCrossingEdges_reverse]

/-- The set-valued separator is precisely the value image of its finite edge
carrier.  This makes the generic deletion-component construction applicable
to the source's annular interface. -/
theorem primalCut_eq_edgeFinsetValueSet_primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    pair.primalCut data = edgeFinsetValueSet (pair.primalCutEdges data) := by
  change dualWalkPrimalCut data hunique pair.dualLoop =
    edgeFinsetValueSet
      (dualWalkCrossingEdges
        (orbitFaceBoundary data.toRotationSystem)
        (Finset.univ : Finset (OrbitFace data.toRotationSystem)) hunique pair.dualLoop)
  exact dualWalkPrimalCut_eq_edgeFinsetValueSet_dualWalkCrossingEdges
    data hunique pair.dualLoop

/-- A genuine annular separator produces two different connected components
after the crossed primal edges are removed. -/
theorem exists_distinct_primalCutComponents
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    ∃ inside outside :
        (G.deleteEdges
          (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent,
      inside ≠ outside := by
  apply exists_distinct_components_of_not_connected hconnected
    (pair.primalCutEdges data)
  rw [← pair.primalCut_eq_edgeFinsetValueSet_primalCutEdges data]
  exact pair.primalCut_not_connected data htwoSided hdual hconnected hsphere

/-- Every original-graph edge leaving a constructed deletion component belongs
to the paired transversal's finite primal cut. -/
theorem componentCrossingEdges_subset_primalCutEdges
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    componentCrossingEdges (pair.primalCutEdges data) component ⊆
      pair.primalCutEdges data :=
  componentCrossingEdges_subset_removed (pair.primalCutEdges data) component

/-- The retained graph induced by any constructed side remains connected in
the original graph. -/
theorem connected_induce_primalCutComponent
    (data : Data G)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (component : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent) :
    (G.induce component.supp).Connected :=
  connected_induce_delete_component (pair.primalCutEdges data) component

/-- Distinct deletion components have a genuine original-graph boundary
between them.  Connectivity supplies a path from one component to the other,
and the first change of side along that path is a crossing edge. -/
theorem componentCrossingEdges_nonempty_of_distinct
    (data : Data G)
    (hconnected : G.Connected)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (inside outside : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    (componentCrossingEdges (pair.primalCutEdges data) inside).Nonempty := by
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
    (mem_componentCrossingEdges_iff (pair.primalCutEdges data) inside edge).2
      hcross⟩

/-- A component selected from the paired annular separator has exactly the
separator as its original-graph boundary.  This is the planar bond step: the
inclusion from edge deletion is upgraded to equality by parity propagation
around the simple dual loop. -/
theorem componentCrossingEdges_eq_primalCutEdges_of_distinct
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique)
    (inside outside : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent)
    (hdistinct : inside ≠ outside) :
    componentCrossingEdges (pair.primalCutEdges data) inside =
      pair.primalCutEdges data := by
  let side : V → Prop := fun vertex => vertex ∈ inside.supp
  have hsubset : crossingEdgeFinset G side ⊆ pair.primalCutEdges data := by
    rw [← componentCrossingEdges_eq_crossingEdgeFinset
      (pair.primalCutEdges data) inside]
    exact pair.componentCrossingEdges_subset_primalCutEdges data inside
  have hnonempty : (crossingEdgeFinset G side).Nonempty := by
    rw [← componentCrossingEdges_eq_crossingEdgeFinset
      (pair.primalCutEdges data) inside]
    exact pair.componentCrossingEdges_nonempty_of_distinct data hconnected
      inside outside hdistinct
  have hboundary :=
    crossingEdgeFinset_eq_dualWalkCrossingEdges_of_isCycle_of_subset
      data htwoSided hunique pair.dualLoop pair.dualLoop_isCycle side hsubset
        hnonempty
  change componentCrossingEdges (pair.primalCutEdges data) inside = _
  rw [componentCrossingEdges_eq_crossingEdgeFinset]
  exact hboundary

/-- The paired source transversals therefore construct a retained component
whose boundary is exactly their finite primal separator. -/
theorem exists_primalCutComponent_exactBoundary
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    ∃ component : (G.deleteEdges
        (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent,
      componentCrossingEdges (pair.primalCutEdges data) component =
        pair.primalCutEdges data := by
  rcases pair.exists_distinct_primalCutComponents data htwoSided hdual
      hconnected hsphere with ⟨inside, outside, hdistinct⟩
  exact ⟨inside,
    pair.componentCrossingEdges_eq_primalCutEdges_of_distinct data htwoSided
      hconnected inside outside hdistinct⟩

/-- Choose the actual deletion side containing the distinguished outer dart.
The paired source transversals leave a genuinely different component on the
other side, so this supplies both the retained outer region and an actual
removed vertex for the splice rather than asking callers for a side predicate. -/
theorem exists_outer_primalCutComponent_exactBoundary_and_removed
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    {start finish : AmbientFace
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))}
    (pair : SeparatedAlignedSimpleDualCrosscuts
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))
      start finish hunique) :
    ∃ component : (G.deleteEdges
        (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent,
      ∃ removed : V,
        data.toRotationSystem.vertOf data.toRotationSystem.outer ∈ component.supp ∧
        removed ∉ component.supp ∧
        componentCrossingEdges (pair.primalCutEdges data) component =
          pair.primalCutEdges data := by
  let outerVertex := data.toRotationSystem.vertOf data.toRotationSystem.outer
  let outerComponent : (G.deleteEdges
      (edgeFinsetValueSet (pair.primalCutEdges data))).ConnectedComponent :=
    (G.deleteEdges (edgeFinsetValueSet (pair.primalCutEdges data))).connectedComponentMk
      outerVertex
  have houterMem : outerVertex ∈ outerComponent.supp := by
    dsimp [outerComponent]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  rcases pair.exists_distinct_primalCutComponents data htwoSided hdual
      hconnected hsphere with ⟨inside, outside, hdistinct⟩
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
    · exact pair.componentCrossingEdges_eq_primalCutEdges_of_distinct data
        htwoSided hconnected outerComponent outside houterNeOutside
  · have houterNeInside : outerComponent ≠ inside := by
      intro heq
      exact hinside heq.symm
    rcases inside.nonempty_supp with ⟨removed, hremoved⟩
    have hremovedNotOuter : removed ∉ outerComponent.supp := by
      intro houter
      exact hinside (SimpleGraph.ConnectedComponent.eq_of_common_vertex
        hremoved houter)
    refine ⟨outerComponent, removed, ?_, hremovedNotOuter, ?_⟩
    · simpa [outerVertex] using houterMem
    · exact pair.componentCrossingEdges_eq_primalCutEdges_of_distinct data
        htwoSided hconnected outerComponent inside houterNeInside

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
