import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutLoop
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairAmbientClosureCrossFacePairDifferenceBoundaryFaceFusionChainRebaseFaceCircuitRecoveryTransferPrimalSeparator

/-!
# Annular-crosscut separation

This is the generic planar separation step required by the compositional
splice.  It reuses the already kernel-checked dual-cycle argument: on a
cellular sphere map, the primal edges crossed by a simple facial-dual cycle
disconnect the primal graph.  The preceding crosscut module constructs that
cycle directly from the source's two simple annular transversals.

The result is deliberately stated as an edge deletion, rather than pretending
that either individual open transversal is a closed vertex-side cut.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24DualCycleSeparator
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- Keep the graph-edge carrier's equality instance fixed across the generic
dual-cycle theorem and the source-crosscut specialization. -/
local instance graphEdgeSetDecidableEq (G : SimpleGraph V) :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SeparatedAlignedSimpleDualCrosscuts

/-- The actual primal edge support crossed by the closed dual loop between
the two source interfaces. -/
def primalCut
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
    Set (Sym2 V) :=
  dualWalkPrimalCut data hunique pair.dualLoop

/-- The two source interfaces force a genuine primal separation.  This is
the missing geometric direction needed before a retained side and its splice
can be constructed: the conclusion is proved from the explicit dual loop,
not inserted as a field of the interface. -/
theorem primalCut_not_connected
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
    ¬ (G.deleteEdges (pair.primalCut data)).Connected := by
  exact not_connected_deleteEdges_dualWalkPrimalCut_of_isCycle
    data htwoSided hdual hconnected hsphere hunique pair.dualLoop
      pair.dualLoop_isCycle

/-- The separator carries one distinct primal edge per dual-loop step.  Its
size is consequently the sum of the two transverse interface widths. -/
theorem primalCut_ncard_eq_interfaceWidths
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
    (pair.primalCut data).ncard =
      pair.left.walk.length + pair.right.walk.length := by
  rw [primalCut,
    ncard_dualWalkPrimalCut_eq_length_of_isCycle data hunique pair.dualLoop
      pair.dualLoop_isCycle,
    pair.dualLoop_length]

end SeparatedAlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
