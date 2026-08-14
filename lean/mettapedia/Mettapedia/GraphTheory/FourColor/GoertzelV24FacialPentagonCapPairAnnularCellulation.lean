import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairGraphHoleFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairOpenEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularExcess

/-!
# The literal two-cap annular cellulation

The preceding cap-surgery development computes two distinct opened face
orbits and the exact Euler comparison.  This module packages those results as
the `FramedAnnularCellulation` consumed by the corridor layer.

The construction deliberately retains two source-formation premises.  The
selected cap pair must have remotely separated boundary faces, and its
simultaneous retained complement must be connected.  The former is also used
by the face count; the latter makes the opened primal graph connected.  C-4
must derive both facts for the corridor-selected pair.  Thus this is the
literal C-3 constructor, but not the C-4 selection theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairAnnularCellulation

open SimpleGraphDartRotation
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapPairBoundaryFaces
open GoertzelV24FacialPentagonCapPairGraphHoleFaces
open GoertzelV24FacialPentagonCapPairGraphHoleFaces.FacialPentagonCapBoundaryWalkPair
open GoertzelV24FacialPentagonCapPairOpenEuler
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FramedAnnularExcess
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionGraphFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24TwoPentagonCapOpeningCounts
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

namespace FacialPentagonCapBoundaryWalkPair

variable {data : Data G}

private abbrev keep (caps : FacialPentagonCapBoundaryWalkPair data) : V → Prop :=
  GoertzelV24DeletedRegionSlitOpenRegionComparison.keep
    caps.toPentagonCapPair.deletedVertexSupport

local instance retainedVertexFintypeLocal
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    Fintype (RetainedVertex (keep caps)) :=
  GoertzelV24OpenRegionRotation.retainedVertexFintype (keep caps)

local instance retainedVertexDecidableEqLocal
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    DecidableEq (RetainedVertex (keep caps)) :=
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq (keep caps)

local instance openPrimalGraphDecidableRel
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (root : Dart data.toRotationSystem (keep caps)) :
    DecidableRel (PrimalGraph data.toRotationSystem (keep caps) root).Adj :=
  Classical.decRel _

/-- The graph-backed literal opening has the same spherical Euler count as
the ambient map.  The two hole faces remain included in this face count; the
annular Euler characteristic is obtained by removing those two face interiors.
-/
theorem graphBacked_euler
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (root : Dart data.toRotationSystem (keep caps)) :
    (Fintype.card (Vertex data.toRotationSystem (keep caps)) : Int) -
        Fintype.card
          (PrimalGraph data.toRotationSystem (keep caps) root).edgeSet +
        Fintype.card
          (OrbitFace (graphData data (keep caps) root).toRotationSystem) = 2 := by
  have hvertices := PentagonCapPair.card_openPrimalGraph_vertices
    data caps.toPentagonCapPair root
  have hedges := PentagonCapPair.card_openPrimalGraph_edgeSet_add_ten
    data caps.toPentagonCapPair root
  have hvertices' :
      Fintype.card (Vertex data.toRotationSystem (keep caps)) =
        Fintype.card V := by
    exact hvertices
  have hedges' :
      Fintype.card
          (PrimalGraph data.toRotationSystem (keep caps) root).edgeSet +
        10 = Fintype.card G.edgeSet := by
    simpa only [Fintype.card_eq_nat_card] using hedges
  have hopenFaces :=
    GoertzelV24FacialPentagonCapPairOpenEuler.FacialPentagonCapBoundaryWalkPair.card_open_faceCycleLengths_add_ten_eq_ambient
      caps minimal hremote minimal.spherical minimal.facesTwoSided
        (by
          rw [← rotationPrimalGraph_toRotationSystem_eq G data]
          exact minimal.primalConnected)
        minimal.vertexRotationCyclic root
  have hopenOrbitFaces :
      Fintype.card
          (OrbitFace (rotationSystem data.toRotationSystem (keep caps) root)) +
        10 = Fintype.card (OrbitFace data.toRotationSystem) := by
    rw [card_orbitFace_eq_faceCycleLengths_card,
      card_orbitFace_eq_faceCycleLengths_card]
    exact hopenFaces
  have hgraphFaces :
      Fintype.card
          (OrbitFace (graphData data (keep caps) root).toRotationSystem) =
        Fintype.card
          (OrbitFace (rotationSystem data.toRotationSystem (keep caps) root)) := by
    exact (Fintype.card_congr (graphFaceEquiv data (keep caps) root)).symm
  have hambientEuler := minimal.spherical.euler
  omega

/-- C-3 constructor on the literal graph-backed two-cap opening.  It consumes
the two exact C-4 formation facts and introduces no annulus hypothesis. -/
def annularCellulation
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hretained :
      ((rotationPrimalGraph data.toRotationSystem).induce
        {vertex | keep caps vertex}).Connected)
    (root : Dart data.toRotationSystem (keep caps)) :
    FramedAnnularCellulation
      (PrimalGraph data.toRotationSystem (keep caps) root) where
  rotation := graphData data (keep caps) root
  connected := primalGraph_connected_of_retained
    data.toRotationSystem (keep caps) root hretained
  vertexRotation_cyclic := graphData_hasCyclicVertexRotations
    data (keep caps) root minimal.vertexRotationCyclic
  innerHole := graphInnerHoleFace caps root
  outerHole := graphOuterHoleFace caps root
  holes_ne := graphInnerHoleFace_ne_graphOuterHoleFace
    caps minimal hremote root
  euler := graphBacked_euler caps minimal hremote root

end FacialPentagonCapBoundaryWalkPair

end

end GoertzelV24FacialPentagonCapPairAnnularCellulation

end Mettapedia.GraphTheory.FourColor
