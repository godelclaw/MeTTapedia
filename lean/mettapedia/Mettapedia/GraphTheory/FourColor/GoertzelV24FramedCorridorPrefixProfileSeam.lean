import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixBoundaryProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileSeamResidual

/-!
# The exact seam term for a source corridor Cell

The cumulative region after one source Cell is the old prefix together with
the next central hexagon boundary.  This file specializes the exact
three-factor connectivity and face-progress decompositions to that literal
step.  The residual factor is kept visible; no two-factor coverage claim is
made.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorPrefixProfile
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24TerminalProfileFaceUpdate
open GoertzelV24TerminalProfileSeamResidual
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileSeamEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace SourceTrail

namespace AnnularEmbedding

namespace SourceConsecutiveSlabInterface

variable {source : SourceTrail G}
  {embedded : source.AnnularEmbedding} {blockLength : Nat}
  {realization : BoundaryCleanCorridorRealization embedded blockLength}
  {htwoSided : OrbitFacesTwoSided
    embedded.cellulation.rotation.toRotationSystem}
  {hunique : PairwiseUniqueSharedInteriorEdges
    (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
    (Finset.univ : Finset
      (OrbitFace embedded.cellulation.rotation.toRotationSystem))}
  {leftInterior : CorridorInterior blockLength}
  {hnext : leftInterior.center.val + 2 < blockLength}

/-- The cumulative edge region before the displayed source Cell. -/
def localLayerLeftPrefixRegion
    (_interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  corridorPrefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 1)

/-- The literal edge boundary of the central hexagon newly exposed by the
source Cell step. -/
def localLayerCellBoundaryRegion
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem
    interface.nextCenterLayerFace.1

/-- The cumulative edge region after the displayed source Cell. -/
def localLayerRightPrefixRegion
    (_interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : Finset G.edgeSet :=
  corridorPrefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 2)

theorem localLayerRightPrefixRegion_eq_left_union_cell
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerRightPrefixRegion =
      interface.localLayerLeftPrefixRegion ∪
        interface.localLayerCellBoundaryRegion := by
  simpa [localLayerRightPrefixRegion, localLayerLeftPrefixRegion,
    localLayerCellBoundaryRegion] using
    interface.localLayerRightPrefixEdgeRegion_eq_left_union_nextCenterBoundary

/-- The canonical corridor rung shared by the old prefix's last hexagon and
the newly exposed hexagon. -/
def localLayerSharedRungEdge
    (_interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) : G.edgeSet :=
  realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    |>.rungEdge hunique leftInterior.outgoing

theorem localLayerSharedRungEdge_mem_leftPrefix
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerSharedRungEdge ∈
      interface.localLayerLeftPrefixRegion := by
  apply corridorFaceBoundary_subset_prefixEdgeRegion
    realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
    (leftInterior.center.val + 1) leftInterior.center (by omega)
  simpa [localLayerSharedRungEdge] using
    (realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.rungEdge_mem_left hunique leftInterior.outgoing)

theorem localLayerSharedRungEdge_mem_cellBoundary
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerSharedRungEdge ∈
      interface.localLayerCellBoundaryRegion := by
  simpa [localLayerSharedRungEdge, localLayerCellBoundaryRegion,
    nextCenterLayerFace] using
    (realization.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      |>.rungEdge_mem_right hunique leftInterior.outgoing)

/-- The cumulative prefix and the newly exposed source hexagon share exactly
their canonical corridor rung.  Earlier corridor faces cannot also meet the
new hexagon along an edge because the corridor is induced in the facial dual.
-/
theorem localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    interface.localLayerLeftPrefixRegion ∩
        interface.localLayerCellBoundaryRegion =
      {interface.localLayerSharedRungEdge} := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let corridor := realization.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton
  ext edge
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hprefix, hcell⟩
    have hprefix' : edge ∈ corridorPrefixEdgeRegion corridor
        (leftInterior.center.val + 1) := by
      simpa [localLayerLeftPrefixRegion, corridor] using hprefix
    have hcell' : edge ∈ orbitFaceBoundary RS
        (corridor.faceAt (nextCorridorInterior leftInterior hnext).center).1 := by
      simpa [localLayerCellBoundaryRegion, nextCenterLayerFace, RS, corridor]
        using hcell
    rw [mem_corridorPrefixEdgeRegion_iff] at hprefix'
    rcases hprefix' with ⟨position, hposition, hedgePosition⟩
    by_cases hcenter : position = leftInterior.center
    · subst position
      have hinterior : edge ∈ interiorEdgeSupport (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) := by
        apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).2
        exact ⟨Finset.mem_biUnion.2
            ⟨(corridor.faceAt leftInterior.center).1, Finset.mem_univ _,
              hedgePosition⟩,
          orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided edge⟩
      have hshared : edge ∈ sharedInteriorEdges (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))
          (corridor.faceAt leftInterior.outgoing.left).1
          (corridor.faceAt leftInterior.outgoing.right).1 := by
        apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))).2
        refine ⟨hinterior, ?_, ?_⟩
        · simpa using hedgePosition
        · simpa [nextCorridorInterior] using hcell'
      have hrung := corridor.rungEdge_eq_of_shared hunique
        leftInterior.outgoing hshared
      simpa [localLayerSharedRungEdge, corridor] using hrung.symm
    · have hbefore : position.val < leftInterior.center.val := by omega
      have hseparated : position.val + 1 <
          (nextCorridorInterior leftInterior hnext).center.val := by
        change position.val + 1 < leftInterior.center.val + 1
        omega
      have hfacesNe : (corridor.faceAt position).1 ≠
          (corridor.faceAt
            (nextCorridorInterior leftInterior hnext).center).1 := by
        intro hfaces
        have hindices := corridor.faceAt_injective (Subtype.ext hfaces)
        have hvalues := congrArg Fin.val hindices
        change position.val = leftInterior.center.val + 1 at hvalues
        omega
      have hadj :=
        interiorDualGraph_adj_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS))
          (orbitFace_incidence_le_two RS) hfacesNe hedgePosition hcell'
      exact (corridor.separated_not_adjacent position
        (nextCorridorInterior leftInterior hnext).center hseparated hadj).elim
  · intro hedge
    subst edge
    exact ⟨interface.localLayerSharedRungEdge_mem_leftPrefix,
      interface.localLayerSharedRungEdge_mem_cellBoundary⟩

/-- The tracked adjacency factor crossing between the old cumulative prefix
and the newly exposed source hexagon. -/
def localLayerTrackedSeamGraph
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (C : G.edgeSet → Color) (a b : Color) : SimpleGraph G.edgeSet :=
  regionalTrackedSeamGraph
    embedded.cellulation.rotation.toRotationSystem
    interface.localLayerLeftPrefixRegion
    interface.localLayerCellBoundaryRegion C a b

/-- The source Cell's outgoing tracked graph is exactly old-prefix, local
hexagon, and the explicit residual seam factor. -/
theorem localLayerRightPrefixTrackedGraph_eq_three_factor
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (C : G.edgeSet → Color) (a b : Color) :
    regionalTrackedEdgeGraph
        embedded.cellulation.rotation.toRotationSystem
        interface.localLayerRightPrefixRegion C a b =
      (regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          interface.localLayerLeftPrefixRegion C a b ⊔
        regionalTrackedEdgeGraph
          embedded.cellulation.rotation.toRotationSystem
          interface.localLayerCellBoundaryRegion C a b) ⊔
        interface.localLayerTrackedSeamGraph C a b := by
  rw [interface.localLayerRightPrefixRegion_eq_left_union_cell]
  exact regionalTrackedEdgeGraph_union_eq_sup_sup_seam
    embedded.cellulation.rotation.toRotationSystem
    interface.localLayerLeftPrefixRegion
    interface.localLayerCellBoundaryRegion C a b

/-- The face-progress factor crossing between the old cumulative prefix and
the newly exposed source hexagon, on one actual face-cycle carrier. -/
def localLayerFaceSeamGraph
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :=
  faceRegionalSeamGraph
    embedded.cellulation.rotation.toRotationSystem root
    interface.localLayerLeftPrefixRegion
    interface.localLayerCellBoundaryRegion

/-- The outgoing occurrence-sensitive face graph has the same exact
three-factor decomposition as tracked connectivity. -/
theorem localLayerRightPrefixFaceGraph_eq_three_factor
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (root : embedded.cellulation.rotation.toRotationSystem.D) :
    faceRegionalAmbientPositionGraph
        embedded.cellulation.rotation.toRotationSystem root
        interface.localLayerRightPrefixRegion =
      (faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          interface.localLayerLeftPrefixRegion ⊔
        faceRegionalAmbientPositionGraph
          embedded.cellulation.rotation.toRotationSystem root
          interface.localLayerCellBoundaryRegion) ⊔
        interface.localLayerFaceSeamGraph root := by
  rw [interface.localLayerRightPrefixRegion_eq_left_union_cell]
  exact faceRegionalAmbientPositionGraph_union_eq_sup_sup_seam _ _ _ _

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
