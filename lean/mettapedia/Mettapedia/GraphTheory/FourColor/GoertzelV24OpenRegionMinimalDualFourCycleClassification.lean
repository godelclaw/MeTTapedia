import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualFourCycleClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceTransport

/-!
# Minimal dual four-cycle classification survives a literal opening

The closed L1 classification says that an extra common neighbour of two
corridor faces at distance two is adjacent to the displayed middle face.
This file transports that conclusion through a literal vertex-region opening
when the middle and extra faces are fully retained.

Only the conclusion is transported: the four ambient adjacencies and the
minimal-counterexample hypotheses remain statements about the original closed
map.  A source formation theorem must still identify the literal Cell-3 faces
with the retained images below.  Thus this is a generic closed-to-open bridge,
not an assumption that the source opening has already been constructed.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionMinimalDualFourCycleClassification

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalDualFourCycleClassification
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24RotationVertexCutProfile
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq
  GoertzelV24SeamFaceArcPartition.hitPointFintype

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Regard one dart orbit as an ambient face of the full rotation system. -/
def ambientFaceOfDart
    (RS : RotationSystem V G.edgeSet) (root : RS.D) :
    AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
  ⟨dartOrbitFace RS root, Finset.mem_univ _⟩

/-- **L1 (closed-to-open distance-two classification).** If the closed
minimal map has two distinct common neighbours of a nonadjacent endpoint pair,
then the adjacency forced between those common neighbours survives every
literal opening that fully retains both of their facial orbits.

This is the four-cycle counterpart of the retained dual-triangle incidence
bridge.  It supplies the open adjacency needed to classify a distance-two
rail collision; it does not identify any source-local face with an ambient
face image. -/
theorem open_middle_adj_open_other_of_retained_two_common_neighbors
    (graphData : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (keep : V → Prop)
    (outer : GoertzelV24OpenRegionRotation.Dart
      graphData.toRotationSystem keep)
    (firstRoot middleRoot lastRoot otherRoot :
      graphData.toRotationSystem.D)
    (hmiddleRetained : FaceFullyRetained
      graphData.toRotationSystem keep middleRoot)
    (hotherRetained : FaceFullyRetained
      graphData.toRotationSystem keep otherRoot)
    (hfirstMiddle : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem firstRoot)
        (ambientFaceOfDart graphData.toRotationSystem middleRoot))
    (hmiddleLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem middleRoot)
        (ambientFaceOfDart graphData.toRotationSystem lastRoot))
    (hfirstOther : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem firstRoot)
        (ambientFaceOfDart graphData.toRotationSystem otherRoot))
    (hotherLast : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem otherRoot)
        (ambientFaceOfDart graphData.toRotationSystem lastRoot))
    (hnotFirstLast : ¬ (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem firstRoot)
        (ambientFaceOfDart graphData.toRotationSystem lastRoot))
    (hfirstNeLast : dartOrbitFace graphData.toRotationSystem firstRoot ≠
      dartOrbitFace graphData.toRotationSystem lastRoot)
    (hotherNeMiddle : dartOrbitFace graphData.toRotationSystem otherRoot ≠
      dartOrbitFace graphData.toRotationSystem middleRoot) :
    (interiorDualGraph
      (orbitFaceBoundary (rotationSystem graphData.toRotationSystem keep outer))
      (Finset.univ : Finset
        (OrbitFace (rotationSystem graphData.toRotationSystem keep outer)))).Adj
        ⟨openFaceOrbit graphData.toRotationSystem keep outer middleRoot
          hmiddleRetained, Finset.mem_univ _⟩
        ⟨openFaceOrbit graphData.toRotationSystem keep outer otherRoot
          hotherRetained, Finset.mem_univ _⟩ := by
  have hmiddleOther : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace graphData.toRotationSystem))).Adj
        (ambientFaceOfDart graphData.toRotationSystem middleRoot)
        (ambientFaceOfDart graphData.toRotationSystem otherRoot) :=
    middle_adj_other_of_two_common_neighbors graphData minimal
      hfirstMiddle hmiddleLast hfirstOther hotherLast hnotFirstLast
      (by exact fun h => hfirstNeLast (congrArg Subtype.val h))
      (by exact fun h => hotherNeMiddle (congrArg Subtype.val h))
  apply (openFaceOrbit_adj_iff_ambientFaceOrbit_adj
    graphData.toRotationSystem keep outer middleRoot otherRoot
      hmiddleRetained hotherRetained hotherNeMiddle.symm).2
  exact hmiddleOther

end

end GoertzelV24OpenRegionMinimalDualFourCycleClassification

end Mettapedia.GraphTheory.FourColor
