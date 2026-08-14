import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpeningCounts
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapOpenEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionGraphFaceTransport

/-!
# Euler transport across Addendum V's one-cap opening

Opening the interior facial pentagon of Addendum V's frontier preserves the
Euler count: the manuscript-side carrier has the same number of vertices,
exactly five fewer edges, and exactly five fewer faces.  The first two facts
are graph-isomorphism and deletion arithmetic; the third is the literal
one-cap face surgery.

The theorem below deliberately takes the ambient frontier Euler equation as
an explicit premise.  It transports that equation to the opened annulus; it
does not construct the source frontier, prove that premise, or package the two
named hole faces as a `FramedAnnularCellulation`.  This separation prevents a
conditional arithmetic wrapper from being mistaken for the missing source
formation theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapAnnularEuler

open SimpleGraphDartRotation
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FacialPentagonCap
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FrontierPentagonCapInnerFace
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24FrontierPentagonCapOpeningCounts
open GoertzelV24FrontierPentagonCapOpenEuler
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionGraphFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

variable {data : Data G}

private abbrev capOf (walk : FacialPentagonCapBoundaryWalk data) : PentagonCap G :=
  walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap

private abbrev keepCap (walk : FacialPentagonCapBoundaryWalk data) : V → Prop :=
  keep (capOf walk).vertexSupport

local instance retainedVertexFintypeLocal
    (walk : FacialPentagonCapBoundaryWalk data) :
    Fintype (RetainedVertex (keepCap walk)) :=
  GoertzelV24OpenRegionRotation.retainedVertexFintype (keepCap walk)

local instance retainedVertexDecidableEqLocal
    (walk : FacialPentagonCapBoundaryWalk data) :
    DecidableEq (RetainedVertex (keepCap walk)) :=
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq (keepCap walk)

local instance openPrimalGraphDecidableRel
    (walk : FacialPentagonCapBoundaryWalk data)
    (root : Dart data.toRotationSystem (keepCap walk)) :
    DecidableRel
      (PrimalGraph data.toRotationSystem (keepCap walk) root).Adj :=
  Classical.decRel _

/-- **Conditional Euler transport, not source formation.** If the ambient
frontier has spherical Euler count `2`, then its literal one-cap opening has
the same graph-backed Euler count. -/
theorem graphBacked_euler_of_ambient_euler
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (root : Dart data.toRotationSystem (keepCap walk))
    (hambientEuler :
      (Fintype.card V : Int) - Fintype.card G.edgeSet +
        Fintype.card (OrbitFace data.toRotationSystem) = 2) :
    (Fintype.card (Vertex data.toRotationSystem (keepCap walk)) : Int) -
        Fintype.card
          (PrimalGraph data.toRotationSystem (keepCap walk) root).edgeSet +
        Fintype.card
          (OrbitFace (graphData data (keepCap walk) root).toRotationSystem) = 2 := by
  have hvertices :=
    GoertzelV24FrontierPentagonCapOpeningCounts.PentagonCap.card_openPrimalGraph_vertices
      data (capOf walk) root
  have hedges :=
    GoertzelV24FrontierPentagonCapOpeningCounts.PentagonCap.card_openPrimalGraph_edgeSet_add_five
      data (capOf walk) root
  have hvertices' :
      Fintype.card (Vertex data.toRotationSystem (keepCap walk)) =
        Fintype.card V := by
    simpa [keepCap] using hvertices
  have hedges' :
      Fintype.card
          (PrimalGraph data.toRotationSystem (keepCap walk) root).edgeSet + 5 =
        Fintype.card G.edgeSet := by
    simpa only [Fintype.card_eq_nat_card] using hedges
  have hopenFaces := card_open_faceCycleLengths_add_five_eq_ambient
    frontier hfrontier walk hinterior hrotation hunique root
  have hopenOrbitFaces :
      Fintype.card
          (OrbitFace (rotationSystem data.toRotationSystem (keepCap walk) root)) + 5 =
        Fintype.card (OrbitFace data.toRotationSystem) := by
    rw [card_orbitFace_eq_faceCycleLengths_card,
      card_orbitFace_eq_faceCycleLengths_card]
    exact hopenFaces
  have hgraphFaces :
      Fintype.card
          (OrbitFace (graphData data (keepCap walk) root).toRotationSystem) =
        Fintype.card
          (OrbitFace (rotationSystem data.toRotationSystem (keepCap walk) root)) := by
    exact (Fintype.card_congr (graphFaceEquiv data (keepCap walk) root)).symm
  omega

end

end GoertzelV24FrontierPentagonCapAnnularEuler

end Mettapedia.GraphTheory.FourColor
