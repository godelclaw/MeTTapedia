import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapAnnularEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapInnerFace
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularExcess

/-!
# Conditional annular cellulation for Addendum V's literal opening

The preceding one-cap modules compute the two hole faces and transport the
Euler count to the graph-backed opening.  This module packages those results
as the `FramedAnnularCellulation` consumed by the corridor layer.

The constructor is deliberately conditional.  It requires the ambient
frontier Euler equation, connectedness of the retained side, complete
retention of the old outer face, and the cap-collar uniqueness invariant.
Those are the precise source-formation outputs still to be constructed; this
module neither assumes they follow from `FrontierBoundaryData.WellFormed` nor
reports their packaging as the source construction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapAnnularCellulation

open SimpleGraphDartRotation
open GoertzelV24DeletedRegionSlitOpenRegionComparison
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FacialPentagonCap
open GoertzelV24FramedAnnularExcess
open GoertzelV24FrontierPentagonCapAnnularEuler
open GoertzelV24FrontierPentagonCapInnerFace
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24FrontierPentagonCapOuterFace
open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionGraphBacking
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

private abbrev outerRoot (walk : FacialPentagonCapBoundaryWalk data)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer) :
    Dart data.toRotationSystem (keepCap walk) :=
  FrontierOuterFaceData.openingOuterRoot (capOf walk) houterRetained

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
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer) :
    DecidableRel
      (PrimalGraph data.toRotationSystem (keepCap walk)
        (outerRoot walk houterRetained)).Adj :=
  Classical.decRel _

/-- **Conditional C-3 package, not C-4 source formation.** Once the four
listed formation premises are supplied on Addendum V's actual frontier, its
literal one-cap opening is a graph-backed annular cellulation with the two
computed hole faces. -/
def annularCellulation
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (houterRetained : FaceFullyRetained data.toRotationSystem
      (keepCap walk) data.toRotationSystem.outer)
    (hretained :
      ((rotationPrimalGraph data.toRotationSystem).induce
        {vertex | keepCap walk vertex}).Connected)
    (hambientEuler :
      (Fintype.card V : Int) - Fintype.card G.edgeSet +
        Fintype.card (OrbitFace data.toRotationSystem) = 2) :
    FramedAnnularCellulation
      (PrimalGraph data.toRotationSystem (keepCap walk)
        (outerRoot walk houterRetained)) where
  rotation := graphData data (keepCap walk) (outerRoot walk houterRetained)
  connected := primalGraph_connected_of_retained
    data.toRotationSystem (keepCap walk) (outerRoot walk houterRetained)
    hretained
  vertexRotation_cyclic := graphData_hasCyclicVertexRotations
    data (keepCap walk) (outerRoot walk houterRetained) hrotation
  innerHole := openingGraphInnerFace walk houterRetained
  outerHole := FrontierOuterFaceData.openingGraphOuterFace
    (capOf walk) houterRetained
  holes_ne := by
    exact fun heq =>
      openingGraphOuterFace_ne_openingGraphInnerFace walk houterRetained heq.symm
  euler := graphBacked_euler_of_ambient_euler
    frontier hfrontier walk hinterior hrotation hunique
      (outerRoot walk houterRetained) hambientEuler

end

end GoertzelV24FrontierPentagonCapAnnularCellulation

end Mettapedia.GraphTheory.FourColor
