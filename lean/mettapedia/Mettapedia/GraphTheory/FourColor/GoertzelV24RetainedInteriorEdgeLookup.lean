import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceIntersectionTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24InteriorDualPointwiseLookup

/-!
# The interior-dual lookup on retained faces

This is the supplier that makes the pointwise interior-dual lookup usable on an
opened annulus without assuming anything globally false there.

Two ingredients are already in place.  Retained-face transport says that two
*fully retained* faces of a literal opening still share at most one interior
edge, because that bound is consumed on the ambient closed carrier where
minimality holds.  The pointwise lookup says a dual adjacency plus that one
bound already determines the primal edge.  Composing them gives an edge lookup
whose hypotheses are all true on the opened carrier.

The boundary-spliced faces are excluded by construction rather than by a side
condition that someone has to remember: they are not fully retained, so they
never satisfy the premise.  This is the point of the refactor.  Assuming
uniqueness globally on the opened annulus is not merely unproved -- the two
opened faces of a dodecahedron share ten interior edges -- so the corridor
machinery has to obtain the bound where it is true, one face pair at a time.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RetainedInteriorEdgeLookup

open GoertzelV24FaceOrbitIncidence
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24HexCorridorSkeleton
open GoertzelV24OpenRegionFaceIntersectionTransport
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24InteriorDualPointwiseLookup
open SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

variable {V E : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- The opened face of a fully retained ambient face, packaged as an ambient
face of the opened carrier. -/
noncomputable def retainedFace
    (graphData : Data G) (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart graphData.toRotationSystem keep)
    (root : graphData.toRotationSystem.D)
    (hroot : FaceFullyRetained graphData.toRotationSystem keep root) :
    AmbientFace (Finset.univ : Finset (OrbitFace
      (rotationSystem graphData.toRotationSystem keep outer))) :=
  ⟨openFaceOrbit graphData.toRotationSystem keep outer root hroot, Finset.mem_univ _⟩

/-- **The pointwise premise on retained faces.**  This is the whole content the
lookup needs, and it is supplied by transport from the closed carrier rather
than assumed on the opened one. -/
theorem card_le_one_of_retained
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart graphData.toRotationSystem keep)
    (leftRoot rightRoot : graphData.toRotationSystem.D)
    (hleft : FaceFullyRetained graphData.toRotationSystem keep leftRoot)
    (hright : FaceFullyRetained graphData.toRotationSystem keep rightRoot)
    (hne : dartOrbitFace graphData.toRotationSystem leftRoot ≠
      dartOrbitFace graphData.toRotationSystem rightRoot) :
    (sharedInteriorEdges
      (orbitFaceBoundary
        (rotationSystem graphData.toRotationSystem keep outer))
      (Finset.univ : Finset (OrbitFace
        (rotationSystem graphData.toRotationSystem keep outer)))
      (retainedFace graphData keep outer leftRoot hleft).1
      (retainedFace graphData keep outer rightRoot hright).1).card ≤ 1 :=
  openMinimalFaceOrbits_sharedInteriorEdges_card_le_one graphData minimal keep outer
    leftRoot rightRoot hleft hright hne

/-- **The retained interior-dual edge.**  A dual adjacency between two fully
retained faces of a literal opening determines a primal edge, with no global
uniqueness hypothesis anywhere. -/
noncomputable def retainedInteriorEdge
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart graphData.toRotationSystem keep)
    (leftRoot rightRoot : graphData.toRotationSystem.D)
    (hleft : FaceFullyRetained graphData.toRotationSystem keep leftRoot)
    (hright : FaceFullyRetained graphData.toRotationSystem keep rightRoot)
    (hne : dartOrbitFace graphData.toRotationSystem leftRoot ≠
      dartOrbitFace graphData.toRotationSystem rightRoot)
    (hadj : (interiorDualGraph
        (orbitFaceBoundary (rotationSystem graphData.toRotationSystem keep outer))
        (Finset.univ : Finset (OrbitFace
          (rotationSystem graphData.toRotationSystem keep outer)))).Adj
      (retainedFace graphData keep outer leftRoot hleft)
      (retainedFace graphData keep outer rightRoot hright)) :
    (rewiredDartSystem graphData.toRotationSystem keep outer).Edge :=
  sharedInteriorEdgeOfAdj _ _
    (card_le_one_of_retained graphData minimal keep outer leftRoot rightRoot
      hleft hright hne) hadj

/-- The retained lookup is pinned by any explicit shared-edge witness.  This is
the shape every corridor consumer already uses: it proves the lookup equals a
named dart's edge by exhibiting that edge in the shared set. -/
theorem retainedInteriorEdge_eq_of_mem
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    (keep : V → Prop)
    [Fintype (RetainedVertex keep)] [DecidableEq (RetainedVertex keep)]
    (outer : Dart graphData.toRotationSystem keep)
    (leftRoot rightRoot : graphData.toRotationSystem.D)
    (hleft : FaceFullyRetained graphData.toRotationSystem keep leftRoot)
    (hright : FaceFullyRetained graphData.toRotationSystem keep rightRoot)
    (hne : dartOrbitFace graphData.toRotationSystem leftRoot ≠
      dartOrbitFace graphData.toRotationSystem rightRoot)
    (hadj : (interiorDualGraph
        (orbitFaceBoundary (rotationSystem graphData.toRotationSystem keep outer))
        (Finset.univ : Finset (OrbitFace
          (rotationSystem graphData.toRotationSystem keep outer)))).Adj
      (retainedFace graphData keep outer leftRoot hleft)
      (retainedFace graphData keep outer rightRoot hright))
    {e : (rewiredDartSystem graphData.toRotationSystem keep outer).Edge}
    (he : e ∈ sharedInteriorEdges
      (orbitFaceBoundary (rotationSystem graphData.toRotationSystem keep outer))
      (Finset.univ : Finset (OrbitFace
        (rotationSystem graphData.toRotationSystem keep outer)))
      (retainedFace graphData keep outer leftRoot hleft).1
      (retainedFace graphData keep outer rightRoot hright).1) :
    retainedInteriorEdge graphData minimal keep outer leftRoot rightRoot
        hleft hright hne hadj = e :=
  sharedInteriorEdgeOfAdj_eq_of_mem _ _ _ hadj he

end GoertzelV24RetainedInteriorEdgeLookup

end Mettapedia.GraphTheory.FourColor
