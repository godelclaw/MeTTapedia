import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairBoundaryOrbitCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapPairPureFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpeningCounts

/-!
# Exact face and Euler counts for the literal two-cap opening

For a source-facing pair of remote facial pentagon caps, the ambient face
partition has ten transition faces, two pure cap faces, and the wholly
retained faces.  The literal opening has those same wholly retained faces and
exactly two boundary-successor faces.  Hence opening the two caps removes ten
edges and ten faces while preserving the vertex count.

This is the numerical C-3 annulus calculation.  It consumes the explicit C-4
remote-boundary premise used to identify the ten transition faces and the two
boundary orbits; it does not construct that premise or package the source
annular embedding.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapPairOpenEuler

open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CurvatureScope
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapPairBoundaryFaces
open GoertzelV24FacialPentagonCapPairBoundaryOrbitCount
open GoertzelV24FacialPentagonCapPairFaceCounts
open GoertzelV24FacialPentagonCapPairOpenHoleOrbit
open GoertzelV24FacialPentagonCapPairOpenHoleOrbit.FacialPentagonCapBoundaryWalkPair
open GoertzelV24FacialPentagonCapPairPureFaces
open GoertzelV24OpenRegionFaceCount
open GoertzelV24OpenRegionGraphBacking
open GoertzelV24OpenRegionRotation
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24TwoPentagonCapOpening
open GoertzelV24TwoPentagonCapOpeningCounts
open GoertzelV24TwoEdgeCutMinimality

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

namespace FacialPentagonCapBoundaryWalkPair

variable {data : Data G}

private abbrev keep (caps : FacialPentagonCapBoundaryWalkPair data) : V → Prop :=
  deletedRegionKeep caps.toPentagonCapPair.deletedVertexSupport

local instance retainedVertexFintypeLocal
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    Fintype (RetainedVertex (keep caps)) :=
  Fintype.ofFinite _

local instance retainedVertexDecidableEqLocal
    (caps : FacialPentagonCapBoundaryWalkPair data) :
    DecidableEq (RetainedVertex (keep caps)) :=
  Subtype.instDecidableEq

/-- The literal two-cap opening has exactly ten fewer quotient faces than the
ambient spherical rotation. -/
theorem card_open_faceCycleLengths_add_ten_eq_ambient
    (caps : FacialPentagonCapBoundaryWalkPair data)
    (minimal : GraphBackedVertexMinimalTaitCounterexample data)
    (hremote : RemoteBoundaryFacesSeparated data
      caps.toOrientedFacialPentagonCapPair)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (root : Dart data.toRotationSystem (keep caps)) :
    (faceCycleLengths
        (rotationSystem data.toRotationSystem (keep caps) root)).card + 10 =
      (faceCycleLengths data.toRotationSystem).card := by
  let deleted := caps.toPentagonCapPair.deletedVertexSupport
  have hopen := card_openRegion_faceCycleLengths_eq_allOnSide_add_boundary
    data.toRotationSystem (keep caps) root
  have hboundary :=
    GoertzelV24FacialPentagonCapPairBoundaryOrbitCount.FacialPentagonCapBoundaryWalkPair.card_boundarySuccessor_partition_eq_two
      caps minimal hremote hsphere.cubic hrotation
  have htouched :=
    OrientedFacialPentagonCapPair.card_cutSideTransitionFaces_eq_ten
      caps.toOrientedFacialPentagonCapPair minimal hremote
  have hpure :=
    GoertzelV24FacialPentagonCapPairPureFaces.FacialPentagonCapBoundaryWalkPair.card_orbitFacesAllOnDeletedSupport_eq_two
      caps hsphere htwoSided hconnected hrotation
  have hambient := card_transition_add_allOnSide_add_allOffSide_eq_faces
    data.toRotationSystem deleted
  have hboundary' :
      (retainedRegionBoundarySuccessor data.toRotationSystem
        (keep caps)).partition.parts.card = 2 := by
    exact hboundary
  have htouched' :
      (cutSideTransitionFaces data.toRotationSystem deleted).card = 10 := by
    exact htouched
  have hpure' :
      (orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => ¬ deletedRegionKeep deleted vertex)).card = 2 := by
    simpa [deletedRegionKeep] using hpure
  rw [hboundary'] at hopen
  rw [htouched', hpure'] at hambient
  have hambient' :
      10 + (orbitFacesAllOnSide data.toRotationSystem (keep caps)).card + 2 =
        (faceCycleLengths data.toRotationSystem).card := by
    change 10 +
        (orbitFacesAllOnSide data.toRotationSystem (keep caps)).card + 2 =
      data.toRotationSystem.phi.partition.parts.card
    rw [← card_permOrbit_eq_card_partition_parts]
    exact hambient
  omega

end FacialPentagonCapBoundaryWalkPair

end

end GoertzelV24FacialPentagonCapPairOpenEuler

end Mettapedia.GraphTheory.FourColor
