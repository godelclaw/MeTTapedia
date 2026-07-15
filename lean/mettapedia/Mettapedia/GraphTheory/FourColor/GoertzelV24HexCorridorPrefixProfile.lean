import Mettapedia.GraphTheory.FourColor.GoertzelV24GraphDerivedCorridorCutProfile

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorPrefixProfile

open GoertzelV24CorridorProfile
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorFiniteColorTransition
open GoertzelV24HexCorridorColorTransfer
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24HexSlabSideAdjacency

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Corridor faces whose index lies strictly before a numerical cut. -/
def corridorPrefixFaceIndices (corridorLength cut : Nat) :
    Finset (Fin corridorLength) :=
  Finset.univ.filter fun position => position.val < cut

@[simp]
theorem mem_corridorPrefixFaceIndices_iff
    {corridorLength cut : Nat} (position : Fin corridorLength) :
    position ∈ corridorPrefixFaceIndices corridorLength cut ↔
      position.val < cut := by
  simp [corridorPrefixFaceIndices]

/-- The primal edge region exposed by a corridor prefix: the union of the
actual quotient-face boundaries strictly before the cut. This is a strip
region, not a claim that the corridor separates the ambient map. -/
def corridorPrefixEdgeRegion
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength) (cut : Nat) :
    Finset E :=
  (corridorPrefixFaceIndices corridorLength cut).biUnion fun position =>
    orbitFaceBoundary RS (corridor.faceAt position).1

@[simp]
theorem mem_corridorPrefixEdgeRegion_iff
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (cut : Nat) (edge : E) :
    edge ∈ corridorPrefixEdgeRegion corridor cut ↔
      ∃ position : Fin corridorLength,
        position.val < cut ∧
          edge ∈ orbitFaceBoundary RS (corridor.faceAt position).1 := by
  simp [corridorPrefixEdgeRegion]

/-- Later corridor cuts contain every edge exposed by an earlier cut. -/
theorem corridorPrefixEdgeRegion_mono
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    {earlier later : Nat} (hcut : earlier ≤ later) :
    corridorPrefixEdgeRegion corridor earlier ⊆
      corridorPrefixEdgeRegion corridor later := by
  intro edge hedge
  rw [mem_corridorPrefixEdgeRegion_iff] at hedge ⊢
  rcases hedge with ⟨position, hposition, hedge⟩
  exact ⟨position, hposition.trans_le hcut, hedge⟩

/-- Every edge of a corridor face before the cut belongs to the prefix edge
region. -/
theorem corridorFaceBoundary_subset_prefixEdgeRegion
    {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (cut : Nat) (position : Fin corridorLength)
    (hposition : position.val < cut) :
    orbitFaceBoundary RS (corridor.faceAt position).1 ⊆
      corridorPrefixEdgeRegion corridor cut := by
  intro edge hedge
  exact (mem_corridorPrefixEdgeRegion_iff corridor cut edge).2
    ⟨position, hposition, hedge⟩

/-- All six actual boundary edges of an internal corridor face are present
when the prefix cut is placed immediately after that face. -/
theorem placedHexBoundaryEdge_mem_centerPrefix
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : Fin 6) :
    faceCycleEdge RS placement.root
        (placementPositionOfSix placement position) ∈
      corridorPrefixEdgeRegion corridor (interior.center.val + 1) := by
  apply corridorFaceBoundary_subset_prefixEdgeRegion corridor
    (interior.center.val + 1) interior.center (by omega)
  rw [← placement.root_face]
  exact faceCycleEdge_mem RS placement.root
    (placementPositionOfSix placement position)

/-- The six-edge profile of an internal corridor face, with connectivity
computed through the entire graph-backed corridor prefix ending at that face. -/
def placedHexCenterPrefixCutProfile
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    CorridorCutProfile 6 0 0 :=
  placedHexBoundaryCutProfile placement
    (corridorPrefixEdgeRegion corridor (interior.center.val + 1)) C hC

@[simp]
theorem placedHexCenterPrefixCutProfile_edgeColor
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    (placedHexCenterPrefixCutProfile placement C hC).edgeColor =
      placedHexColorWord placement C hC :=
  rfl

/-- A diagonal port entry of the center-prefix profile is true exactly for
the two tracked color pairs containing that port's actual edge color. -/
theorem placedHexCenterPrefixCutProfile_self_eq_true_iff
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair) (position : Fin 6) :
    (placedHexCenterPrefixCutProfile placement C hC).strandConnected pair
        (.inl position) (.inl position) = true ↔
      IsTrackedColor (trackedColorPairColors pair).1
        (trackedColorPairColors pair).2
        (C (faceCycleEdge RS placement.root
          (placementPositionOfSix placement position))) := by
  change regionalTrackedConnectivity RS
      (corridorPrefixEdgeRegion corridor (interior.center.val + 1)) C pair
        (faceCycleEdge RS placement.root
          (placementPositionOfSix placement position))
        (faceCycleEdge RS placement.root
          (placementPositionOfSix placement position)) = true ↔ _
  simpa [placedHexBoundaryEdge_mem_centerPrefix placement position] using
    regionalTrackedConnectivity_self_eq_true_iff RS
      (corridorPrefixEdgeRegion corridor (interior.center.val + 1)) C pair
      (faceCycleEdge RS placement.root
        (placementPositionOfSix placement position))

/-- Consecutive boundary edges carrying a selected color pair are connected
in the actual center-prefix region. This is the local non-vacuity property
needed by any later transfer or splice theorem. -/
theorem placedHexCenterPrefixCutProfile_connected_of_cyclicSuccessor
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (hcubic : RS.IsCubic) (hrotation : VertexRotationCyclic RS)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (pair : TrackedColorPair) (left right : Fin 6)
    (hsuccessor : right.val ≡ left.val + 1 [MOD 6])
    (hleftColor : IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
      (C (faceCycleEdge RS placement.root
        (placementPositionOfSix placement left))))
    (hrightColor : IsTrackedColor (trackedColorPairColors pair).1
      (trackedColorPairColors pair).2
      (C (faceCycleEdge RS placement.root
        (placementPositionOfSix placement right)))) :
    (placedHexCenterPrefixCutProfile placement C hC).strandConnected pair
      (.inl left) (.inl right) = true := by
  let leftPosition := placementPositionOfSix placement left
  let rightPosition := placementPositionOfSix placement right
  let leftEdge := faceCycleEdge RS placement.root leftPosition
  let rightEdge := faceCycleEdge RS placement.root rightPosition
  have hdarts : faceCycleDart RS placement.root rightPosition =
      RS.phi (faceCycleDart RS placement.root leftPosition) :=
    faceCycleDart_successor_of_modEq RS placement.root placement.orbit_card
      leftPosition rightPosition (by simpa [leftPosition, rightPosition] using hsuccessor)
  have hcorner := cornerEdges_pairwise_ne_and_incident RS hcubic hrotation
    (faceCycleDart RS placement.root leftPosition)
  have hedgeAdj : RS.edgeAdjacencyGraph.Adj leftEdge rightEdge := by
    apply RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    · simpa only [leftEdge, rightEdge, faceCycleEdge, hdarts] using hcorner.1
    · simpa only [leftEdge, faceCycleEdge] using hcorner.2.2.2.1
    · simpa only [rightEdge, faceCycleEdge, hdarts] using
        hcorner.2.2.2.2.1
  have hleftMem : leftEdge ∈
      corridorPrefixEdgeRegion corridor (interior.center.val + 1) := by
    exact placedHexBoundaryEdge_mem_centerPrefix placement left
  have hrightMem : rightEdge ∈
      corridorPrefixEdgeRegion corridor (interior.center.val + 1) := by
    exact placedHexBoundaryEdge_mem_centerPrefix placement right
  change regionalTrackedConnectivity RS
      (corridorPrefixEdgeRegion corridor (interior.center.val + 1)) C pair
        leftEdge rightEdge = true
  apply (regionalTrackedConnectivity_eq_true_iff RS
    (corridorPrefixEdgeRegion corridor (interior.center.val + 1)) C pair
      leftEdge rightEdge).2
  exact ⟨hleftMem, hrightMem, hleftColor, hrightColor,
    SimpleGraph.Adj.reachable
      ⟨⟨hedgeAdj, hleftColor, hrightColor⟩, hleftMem, hrightMem⟩⟩

/-- The center-prefix cut as an instance of the full graph-derived cut-data
carrier. There are six crossing ports and no fixed terminals or open face
fragments in this local realization. -/
def placedHexCenterPrefixGraphCutData
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    GraphCorridorCutData RS 6 0 0 where
  regionEdges :=
    corridorPrefixEdgeRegion corridor (interior.center.val + 1)
  crossingEdge position := faceCycleEdge RS placement.root
    (placementPositionOfSix placement position)
  terminalEdge impossible := Fin.elim0 impossible
  fragmentFace impossible := Fin.elim0 impossible
  fragmentEdges impossible := Fin.elim0 impossible

theorem placedHexCenterPrefixGraphCutData_portsInRegion
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior) :
    (placedHexCenterPrefixGraphCutData placement).PortsInRegion := by
  intro port
  rcases port with crossing | impossible
  · exact placedHexBoundaryEdge_mem_centerPrefix placement crossing
  · exact Fin.elim0 impossible

/-- The earlier six-port center-prefix profile is exactly the
zero-terminal, zero-fragment instance of the complete graph-derived profile. -/
theorem placedHexCenterPrefixGraphCutData_profile_eq
    {RS : RotationSystem V E} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C) :
    (placedHexCenterPrefixGraphCutData placement).profile C hC =
      placedHexCenterPrefixCutProfile placement C hC := by
  unfold GraphCorridorCutData.profile placedHexCenterPrefixGraphCutData
    placedHexCenterPrefixCutProfile placedHexBoundaryCutProfile
  rw [CorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · funext pair left right
    rcases left with left | impossible
    · rcases right with right | impossible
      · rfl
      · exact Fin.elim0 impossible
    · exact Fin.elim0 impossible
  · funext impossible
    exact Fin.elim0 impossible
  · funext impossible
    exact Fin.elim0 impossible
  · funext impossible
    exact Fin.elim0 impossible

end

end GoertzelV24HexCorridorPrefixProfile

end Mettapedia.GraphTheory.FourColor
