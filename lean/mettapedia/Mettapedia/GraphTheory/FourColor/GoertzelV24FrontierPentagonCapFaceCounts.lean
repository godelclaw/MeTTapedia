import Mettapedia.GraphTheory.FourColor.GoertzelV24CutTransitionFaceCount
import Mettapedia.GraphTheory.FourColor.GoertzelV24FrontierPentagonCapInnerFace

/-!
# Intrinsic face counts at Addendum V's opened cap

The frontier tangle in Addendum V is already open at its outer boundary, so
the closed spherical hypotheses used by the earlier two-cap laboratory do not
apply.  This module records the three cap-local counts that survive on the
literal frontier carrier.

The five ordered cap spokes enumerate the whole cut boundary.  Under the
exact local collar condition `CapBoundaryFacesUnique`, they therefore touch
five distinct ambient faces.  The computed complementary boundary order and
local cap-vertex cubicity also show that the retained first-return permutation
has one orbit.  These are the boundary terms needed by the one-cap face
surgery calculation.

This file does not count wholly deleted faces, assert an Euler equation, or
construct the source-selected frontier tangle.  In particular, it does not
replace those remaining geometric obligations by closed-map assumptions.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FrontierPentagonCapFaceCounts

open SimpleGraphDartRotation
open GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24CutTransitionFaceCount
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapDeletedBoundaryCycle
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24FrontierPentagonCapInnerFace
open GoertzelV24FrontierPentagonCapOpening
open GoertzelV24OpenRegionRotation
open GoertzelV24PentagonCapOpening
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationVertexCutProfile

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

variable {data : Data G}

private abbrev capOf (walk : FacialPentagonCapBoundaryWalk data) : PentagonCap G :=
  walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap

private abbrev keep (walk : FacialPentagonCapBoundaryWalk data) : V → Prop :=
  PentagonCap.keep (capOf walk)

/-- The literal one-cap cut has exactly the five source-ordered retained
boundary darts. -/
theorem card_boundaryDart_eq_five
    (walk : FacialPentagonCapBoundaryWalk data) :
    Fintype.card (BoundaryDart data.toRotationSystem (keep walk)) = 5 := by
  rw [← Fintype.card_congr
    (PentagonCap.openBoundaryDartEquiv data (capOf walk))]
  simp

/-- Equivalently, the endpoint-computed crossing-edge set of the one-cap cut
has cardinality five. -/
theorem card_vertexSetCrossingEdges_eq_five
    (walk : FacialPentagonCapBoundaryWalk data) :
    (vertexSetCrossingEdges data.toRotationSystem
      (capOf walk).vertexSupport).card = 5 := by
  rw [← card_boundaryDart_deletedRegionKeep]
  exact card_boundaryDart_eq_five walk

/-- The local collar condition makes the five cap spokes lie on five distinct
ambient touched faces.  No global two-sidedness premise is used. -/
theorem card_cutSideTransitionFaces_eq_five
    (walk : FacialPentagonCapBoundaryWalk data)
    (hunique : CapBoundaryFacesUnique walk) :
    (cutSideTransitionFaces data.toRotationSystem
      (capOf walk).vertexSupport).card = 5 := by
  rw [card_cutSideTransitionFaces_eq_crossingEdges_of_unique]
  · exact card_vertexSetCrossingEdges_eq_five walk
  · exact cutFacesHaveUniqueRetainedBoundaryDart_of_capBoundaryFacesUnique
      walk hunique

/-- Every pair of literal cap-boundary coordinates lies in one cycle of the
retained first-return permutation. -/
theorem retainedBoundarySuccessor_openBoundary_sameCycle
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (first second : Fin 5) :
    (retainedRegionBoundarySuccessor data.toRotationSystem (keep walk)).SameCycle
      (PentagonCap.openBoundaryDart data (capOf walk) first)
      (PentagonCap.openBoundaryDart data (capOf walk) second) := by
  change
    (retainedRegionBoundarySuccessor data.toRotationSystem
      (deletedRegionKeep (capOf walk).vertexSupport)).SameCycle
      (PentagonCap.openBoundaryDart data (capOf walk) first)
      (PentagonCap.openBoundaryDart data (capOf walk) second)
  have horder :=
    retained_boundarySuccessor_eq_deleted_boundarySuccessor_inv_of_cutFacesUnique
      data.toRotationSystem (capOf walk).vertexSupport
      (cutFacesHaveUniqueRetainedBoundaryDart_of_capBoundaryFacesUnique
        walk hunique)
  rw [horder, Equiv.Perm.sameCycle_inv]
  exact deletedRegionBoundarySuccessor_openBoundary_sameCycle walk
    (capVerticesCubic_of_frontierWellFormed frontier hfrontier walk hinterior)
    hrotation first second

/-- The retained first-return permutation is transitive on the entire literal
one-cap boundary carrier. -/
theorem retainedBoundarySuccessor_sameCycle
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk)
    (left right : BoundaryDart data.toRotationSystem (keep walk)) :
    (retainedRegionBoundarySuccessor data.toRotationSystem (keep walk)).SameCycle
      left right := by
  obtain ⟨first, rfl⟩ := PentagonCap.exists_openBoundaryDart_eq data (capOf walk) left
  obtain ⟨second, rfl⟩ := PentagonCap.exists_openBoundaryDart_eq data (capOf walk) right
  exact retainedBoundarySuccessor_openBoundary_sameCycle frontier hfrontier walk
    hinterior hrotation hunique first second

/-- The one-cap retained boundary successor has exactly one orbit.  This is
the numerical boundary-face term needed by Addendum V's open face count. -/
theorem card_boundarySuccessor_partition_eq_one
    (frontier : FrontierBoundaryData G outerCount)
    (hfrontier : frontier.WellFormed)
    (walk : FacialPentagonCapBoundaryWalk data)
    (hinterior : frontier.InteriorPentagonCap (capOf walk))
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hunique : CapBoundaryFacesUnique walk) :
    (retainedRegionBoundarySuccessor data.toRotationSystem
      (keep walk)).partition.parts.card = 1 := by
  let successor := retainedRegionBoundarySuccessor data.toRotationSystem (keep walk)
  let orbit := Quotient (Equiv.Perm.SameCycle.setoid successor)
  have horbitCard : Fintype.card orbit = 1 := by
    let witness : orbit := Quotient.mk _
      (PentagonCap.openBoundaryDart data (capOf walk) 0)
    exact Fintype.card_eq_one_iff.mpr
      ⟨witness, fun other => by
        induction other using Quotient.inductionOn with
        | _ boundary =>
            apply Quotient.sound
            exact retainedBoundarySuccessor_sameCycle frontier hfrontier walk
              hinterior hrotation hunique boundary
              (PentagonCap.openBoundaryDart data (capOf walk) 0)⟩
  rw [← card_permOrbit_eq_card_partition_parts]
  exact horbitCard

end

end GoertzelV24FrontierPentagonCapFaceCounts

end Mettapedia.GraphTheory.FourColor
