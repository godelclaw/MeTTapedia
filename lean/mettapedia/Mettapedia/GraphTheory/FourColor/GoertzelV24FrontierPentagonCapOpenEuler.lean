import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapPureFace
import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceCount

/-!
# One-cap face surgery on Addendum V's frontier

The literal frontier opening has one boundary-successor orbit.  Its ambient
face partition has five transition faces, the wholly retained faces, and one
pure deleted pentagon face.  Therefore opening the interior facial pentagon
removes exactly five quotient faces.

Unlike the earlier closed two-cap laboratory, this theorem is stated on the
already-open Addendum V frontier and uses only cap-local cubicity.  It is the
face-count half of the one-cap Euler comparison.  It does not construct the
ambient frontier cellulation, prove its Euler equation, or select the source
frontier from a minimal counterexample.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapOpenEuler

open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CurvatureScope
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FacialPentagonCap
open GoertzelV24FrontierPentagonCapFaceCounts
open GoertzelV24FrontierPentagonCapInnerFace
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24FrontierPentagonCapPureFace
open GoertzelV24OpenRegionFaceCount
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder

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

private abbrev keep (walk : FacialPentagonCapBoundaryWalk data) : V → Prop :=
  deletedRegionKeep (capOf walk).vertexSupport

/-- **Addendum V one-cap face surgery.** The literal opening has exactly five
fewer quotient faces than the ambient frontier rotation. -/
theorem card_open_faceCycleLengths_add_five_eq_ambient
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (root : Dart data.toRotationSystem (keep walk)) :
    (faceCycleLengths
      (rotationSystem data.toRotationSystem (keep walk) root)).card + 5 =
      (faceCycleLengths data.toRotationSystem).card := by
  let deleted := (capOf walk).vertexSupport
  have hopen := card_openRegion_faceCycleLengths_eq_allOnSide_add_boundary
    data.toRotationSystem (keep walk) root
  have hboundary := card_boundarySuccessor_partition_eq_one
    frontier hfrontier walk hinterior hrotation hunique
  have htouched := card_cutSideTransitionFaces_eq_five walk hunique
  have hpure := card_orbitFacesAllOnVertexSupport_eq_one
    frontier hfrontier walk hinterior hrotation
  have hpureSupport :
      (orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => vertex ∈ deleted)).card = 1 := by
    dsimp [deleted]
    exact hpure
  have hambient := card_transition_add_allOnSide_add_allOffSide_eq_faces
    data.toRotationSystem deleted
  have hboundary' :
      (retainedRegionBoundarySuccessor data.toRotationSystem
        (keep walk)).partition.parts.card = 1 := hboundary
  have htouched' :
      (cutSideTransitionFaces data.toRotationSystem deleted).card = 5 := htouched
  have hpure' :
      (orbitFacesAllOnSide data.toRotationSystem
        (fun vertex => ¬ deletedRegionKeep deleted vertex)).card = 1 := by
    simpa [deletedRegionKeep] using hpureSupport
  rw [hboundary'] at hopen
  rw [htouched', hpure'] at hambient
  have hambient' :
      5 + (orbitFacesAllOnSide data.toRotationSystem (keep walk)).card + 1 =
        (faceCycleLengths data.toRotationSystem).card := by
    change 5 +
        (orbitFacesAllOnSide data.toRotationSystem (keep walk)).card + 1 =
      data.toRotationSystem.phi.partition.parts.card
    rw [← card_permOrbit_eq_card_partition_parts]
    exact hambient
  omega

end

end GoertzelV24FrontierPentagonCapOpenEuler

end Mettapedia.GraphTheory.FourColor
