import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutSeparator
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalCutComponent

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
open GoertzelV24DualCycleSeparator
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

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
