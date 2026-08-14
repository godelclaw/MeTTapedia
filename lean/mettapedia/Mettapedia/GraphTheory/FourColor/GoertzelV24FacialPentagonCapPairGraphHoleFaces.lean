import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairOpenHoleOrbit
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionGraphFaceTransport

/-!
# Graph-backed hole faces of the simultaneous facial-cap opening

C-2 computes the two literal opened collar orbits.  C-3 packages an annular
cellulation on the simple graph computed from that opening.  This module names
the corresponding two faces on the graph-backed carrier and transports the
proved five-port incidence and separation theorems.

This is the source-facing endpoint of carrier transport.  It does not prove
the simultaneous retained complement connected or establish its Euler
equation, and therefore does not construct an annular cellulation by itself.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairGraphHoleFaces

open SimpleGraphDartRotation
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapPairBoundaryFaces
open GoertzelV24FacialPentagonCapPairDeletedCycle
open GoertzelV24FacialPentagonCapPairOpenHoleOrbit
open GoertzelV24FacialPentagonCapPairOpenHoleOrbit.FacialPentagonCapBoundaryWalkPair
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionGraphFaceTransport
open GoertzelV24OpenRegionRotation
open GoertzelV24TwoPentagonCapOpening
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

private abbrev retainedKeep
    (caps : FacialPentagonCapBoundaryWalkPair data) : V → Prop :=
  deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport

local instance graphHoleFacesDecidableRel
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (retainedKeep caps)) :
    DecidableRel
      (PrimalGraph data.toRotationSystem (retainedKeep caps) root).Adj :=
  Classical.decRel _

/-- The inner collar face on the simple graph computed from the literal
simultaneous opening. -/
def graphInnerHoleFace
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (retainedKeep caps)) :
    OrbitFace (graphData data (retainedKeep caps) root).toRotationSystem :=
  dartOrbitFace (graphData data (retainedKeep caps) root).toRotationSystem
    (primalDartEquiv data (retainedKeep caps) root
      (Sum.inr (innerRetainedBoundary caps 0)))

/-- The outer collar face on the same graph-backed carrier. -/
def graphOuterHoleFace
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (retainedKeep caps)) :
    OrbitFace (graphData data (retainedKeep caps) root).toRotationSystem :=
  dartOrbitFace (graphData data (retainedKeep caps) root).toRotationSystem
    (primalDartEquiv data (retainedKeep caps) root
      (Sum.inr (outerRetainedBoundary caps 0)))

/-- Every named inner stub lies on the graph-backed inner hole face. -/
theorem graphInnerHoleFace_stub_eq
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (retainedKeep caps)) (step : Fin 5) :
    dartOrbitFace (graphData data (retainedKeep caps) root).toRotationSystem
        (primalDartEquiv data (retainedKeep caps) root
          (Sum.inr (innerRetainedBoundary caps step))) =
      graphInnerHoleFace caps root := by
  rw [← graphFaceEquiv_dartOrbitFace, graphInnerHoleFace,
    ← graphFaceEquiv_dartOrbitFace]
  exact congrArg (graphFaceEquiv data (retainedKeep caps) root)
    (openedInnerHoleFace_stub_eq caps minimal hremote hcubic hrotation root
      step 0)

/-- Every named outer stub lies on the graph-backed outer hole face. -/
theorem graphOuterHoleFace_stub_eq
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hcubic : data.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (retainedKeep caps)) (step : Fin 5) :
    dartOrbitFace (graphData data (retainedKeep caps) root).toRotationSystem
        (primalDartEquiv data (retainedKeep caps) root
          (Sum.inr (outerRetainedBoundary caps step))) =
      graphOuterHoleFace caps root := by
  rw [← graphFaceEquiv_dartOrbitFace, graphOuterHoleFace,
    ← graphFaceEquiv_dartOrbitFace]
  exact congrArg (graphFaceEquiv data (retainedKeep caps) root)
    (openedOuterHoleFace_stub_eq caps minimal hremote hcubic hrotation root
      step 0)

/-- The two graph-backed collar faces remain distinct. -/
theorem graphInnerHoleFace_ne_graphOuterHoleFace
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (root : GoertzelV24OpenRegionRotation.Dart data.toRotationSystem
      (retainedKeep caps)) :
    graphInnerHoleFace caps root ≠ graphOuterHoleFace caps root := by
  rw [graphInnerHoleFace, graphOuterHoleFace,
    ← graphFaceEquiv_dartOrbitFace, ← graphFaceEquiv_dartOrbitFace]
  exact graphFaceEquiv_ne data (retainedKeep caps) root
    (openedInnerHoleFace_ne_openedOuterHoleFace caps minimal hremote root)

end FacialPentagonCapBoundaryWalkPair

end

end GoertzelV24FacialPentagonCapPairGraphHoleFaces

end Mettapedia.GraphTheory.FourColor
