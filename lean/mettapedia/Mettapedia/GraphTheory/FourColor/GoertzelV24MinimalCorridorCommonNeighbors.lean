import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualTriangleClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24MinimalDualFourCycleClassification
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexSlabSideAdjacency
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpace

/-!
# L1 common-neighbour classification on the closed minimal corridor

The source's bounded Cell-3 classification is most naturally proved before
the annulus is cut open.  Minimality says that the three primal edges crossed
by any facial-dual triangle meet at one vertex.  On a simple cubic facial
boundary, the other boundary edge at either endpoint of a rung is exactly the
immediate cyclic flank.  Combining those two facts classifies the primal edge
from a corridor face to every common dual neighbour of it and its successor.

This is the closed-map theorem only.  It deliberately does not identify the
closed corridor with the literal opened `ClosedWebAtGoodWord` carrier; that
formation transport remains a separate theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MinimalCorridorCommonNeighbors

open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24MinimalDualTriangleClassification
open GoertzelV24MinimalDualFourCycleClassification
open GoertzelV24MinimalFaceIntersections
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrientedHexSlab
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- At a cubic vertex, two distinct edges of one simple quotient-face
boundary exhaust all boundary edges incident with that vertex. -/
private theorem incidentEdges_inter_faceBoundary_eq_pair
    (RS : RotationSystem V G.edgeSet)
    (hcubic : RS.IsCubic) (htwoSided : OrbitFacesTwoSided RS)
    (face : OrbitFace RS) (vertex : V) {first second : G.edgeSet}
    (hfirst : first ∈ RS.incidentEdges vertex ∩ orbitFaceBoundary RS face)
    (hsecond : second ∈ RS.incidentEdges vertex ∩ orbitFaceBoundary RS face)
    (hne : first ≠ second) :
    RS.incidentEdges vertex ∩ orbitFaceBoundary RS face = {first, second} := by
  let incidentFace := RS.incidentEdges vertex ∩ orbitFaceBoundary RS face
  have hpairSubset : ({first, second} : Finset G.edgeSet) ⊆ incidentFace := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · exact hfirst
    · exact hsecond
  have hcardLower : 2 ≤ incidentFace.card := by
    rw [← Finset.card_pair hne]
    exact Finset.card_le_card hpairSubset
  have hcardUpper : incidentFace.card ≤ 3 := by
    calc
      incidentFace.card ≤ (RS.incidentEdges vertex).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = 3 := RS.incidentEdges_card_eq_three_of_isCubic hcubic vertex
  have hcardEven : Even incidentFace.card := by
    exact incidentEdges_inter_orbitFaceBoundary_card_even
      RS htwoSided face vertex
  have hcard : incidentFace.card = 2 := by
    rcases hcardEven with ⟨half, hhalf⟩
    omega
  apply Finset.Subset.antisymm
  · intro edge hedge
    have hpairCard : ({first, second} : Finset G.edgeSet).card = 2 :=
      Finset.card_pair hne
    have heq : ({first, second} : Finset G.edgeSet) = incidentFace :=
      Finset.eq_of_subset_of_card_le hpairSubset (by rw [hpairCard, hcard])
    rw [heq]
    exact hedge
  · exact hpairSubset

/-- **L1 (closed bounded interaction).** For a corridor face and its
successor in a graph-backed vertex-minimal Tait counterexample, the canonical
primal edge from the first face to any common dual neighbour is one of the two
literal face-cycle edges immediately flanking the outgoing rung.

The conclusion is phrased in the same primal-edge language as the literal
Cell-3 consumer.  No open-carrier identification or annular-wall hypothesis is
used here. -/
theorem commonNeighborEdge_eq_outgoing_flank
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton graphData.toRotationSystem
      corridorLength)
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor
      (pairwiseUniqueSharedInteriorEdges graphData minimal) interior)
    (before after : {position // position ∈ placementSidePositions placement})
    (hbefore : placement.outgoingPosition.val ≡ before.1.val + 1 [MOD 6])
    (hafter : after.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6])
    (face : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)))
    (hleft : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
        (corridor.faceAt interior.center) face)
    (hright : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
        (corridor.faceAt interior.outgoing.right) face) :
    sharedInteriorEdgeOfAdjOfPairwiseUnique
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal) hleft =
          graphData.toRotationSystem.edgeOf
            (faceCycleDart graphData.toRotationSystem placement.root before.1) ∨
      sharedInteriorEdgeOfAdjOfPairwiseUnique
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
        (pairwiseUniqueSharedInteriorEdges graphData minimal) hleft =
          graphData.toRotationSystem.edgeOf
            (faceCycleDart graphData.toRotationSystem placement.root after.1) := by
  let RS := graphData.toRotationSystem
  let allFaces : Finset (OrbitFace RS) := Finset.univ
  let hunique := pairwiseUniqueSharedInteriorEdges graphData minimal
  let center := corridor.faceAt interior.center
  let next := corridor.faceAt interior.outgoing.right
  let outgoingDart := faceCycleDart RS placement.root placement.outgoingPosition
  let beforeDart := faceCycleDart RS placement.root before.1
  let afterDart := faceCycleDart RS placement.root after.1
  let outgoingEdge := RS.edgeOf outgoingDart
  let beforeEdge := RS.edgeOf beforeDart
  let afterEdge := RS.edgeOf afterDart
  let targetEdge := sharedInteriorEdgeOfAdjOfPairwiseUnique
    (orbitFaceBoundary RS) allFaces hunique hleft
  have hfirstSecond : (interiorDualGraph (orbitFaceBoundary RS) allFaces).Adj
      center next := by
    exact corridor.consecutive_adjacent interior.center
      interior.outgoing.right rfl
  have htriangle :=
    exists_vertex_mem_three_shared_edges_of_dual_triangle
      graphData minimal hfirstSecond hright hleft.symm
  rcases htriangle with ⟨vertex, hvertexOutgoing, _hvertexRight, hvertexTargetReverse⟩
  have hfirstEdgeEq :
      sharedInteriorEdgeOfAdjOfPairwiseUnique
          (orbitFaceBoundary RS) allFaces hunique hfirstSecond = outgoingEdge := by
    change corridor.rungEdge hunique interior.outgoing =
      faceCycleEdge RS placement.root placement.outgoingPosition
    exact placement.outgoing_edge.symm
  have htargetSymm :
      targetEdge = sharedInteriorEdgeOfAdjOfPairwiseUnique
        (orbitFaceBoundary RS) allFaces hunique hleft.symm := by
    symm
    apply sharedInteriorEdgeOfAdjOfPairwiseUnique_eq_of_mem_sharedInteriorEdges
    have hmem := sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_sharedInteriorEdges
      (orbitFaceBoundary RS) allFaces hunique hleft
    simpa only [sharedInteriorEdges, and_comm] using hmem
  have hvertexOutgoingGraph : vertex ∈
      ((sharedInteriorEdgeOfAdjOfPairwiseUnique
        (orbitFaceBoundary RS) allFaces hunique hfirstSecond).1 : Sym2 V) := by
    simpa only [RS, allFaces, hunique, center, next] using hvertexOutgoing
  have hvertexOutgoingIncident :
      sharedInteriorEdgeOfAdjOfPairwiseUnique
          (orbitFaceBoundary RS) allFaces hunique hfirstSecond ∈
        RS.incidentEdges vertex := by
    exact (mem_toRotationSystem_incidentEdges_iff graphData vertex _).2
      hvertexOutgoingGraph
  have hvertexOutgoing' : vertex ∈ RS.endpoints outgoingEdge := by
    apply (RS.mem_endpoints_iff_mem_incidentEdges).2
    rwa [hfirstEdgeEq] at hvertexOutgoingIncident
  have hvertexTargetReverseGraph : vertex ∈
      ((sharedInteriorEdgeOfAdjOfPairwiseUnique
        (orbitFaceBoundary RS) allFaces hunique hleft.symm).1 : Sym2 V) := by
    simpa only [RS, allFaces, hunique, center, next] using hvertexTargetReverse
  have hvertexTargetReverseIncident :
      sharedInteriorEdgeOfAdjOfPairwiseUnique
          (orbitFaceBoundary RS) allFaces hunique hleft.symm ∈
        RS.incidentEdges vertex := by
    exact (mem_toRotationSystem_incidentEdges_iff graphData vertex _).2
      hvertexTargetReverseGraph
  have hvertexTarget : vertex ∈ RS.endpoints targetEdge := by
    apply (RS.mem_endpoints_iff_mem_incidentEdges).2
    rwa [htargetSymm]
  have houtgoingOn : outgoingDart ∈ RS.dartsOn outgoingEdge := by
    exact (RS.mem_dartsOn).2 rfl
  have hvertexCases : vertex = RS.vertOf outgoingDart ∨
      vertex = RS.vertOf (RS.alpha outgoingDart) := by
    have hvertex := hvertexOutgoing'
    rw [RS.endpoints_eq_pair_of_mem houtgoingOn] at hvertex
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hvertex
  have htargetIncident : targetEdge ∈ RS.incidentEdges vertex :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hvertexTarget
  have htargetBoundary : targetEdge ∈ orbitFaceBoundary RS center.1 := by
    exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
      (orbitFaceBoundary RS) allFaces hunique hleft
  have houtgoingBoundary : outgoingEdge ∈ orbitFaceBoundary RS center.1 := by
    change faceCycleEdge RS placement.root placement.outgoingPosition ∈
      orbitFaceBoundary RS center.1
    rw [← placement.root_face]
    exact faceCycleEdge_mem RS placement.root placement.outgoingPosition
  have htargetNeOutgoing : targetEdge ≠ outgoingEdge := by
    intro hedge
    have htargetFace : outgoingEdge ∈ orbitFaceBoundary RS face.1 := by
      rw [← hedge]
      exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        (orbitFaceBoundary RS) allFaces hunique hleft
    have hnextFace : outgoingEdge ∈ orbitFaceBoundary RS next.1 := by
      rw [← hfirstEdgeEq]
      exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        (orbitFaceBoundary RS) allFaces hunique hfirstSecond
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) allFaces (orbitFace_incidence_le_two RS)
        center.2 next.2 face.2
        (fun h => hfirstSecond.ne (Subtype.ext h))
        houtgoingBoundary hnextFace htargetFace
    rcases hcases with hfaceCenter | hfaceNext
    · exact hleft.ne (Subtype.ext hfaceCenter.symm)
    · exact hright.ne (Subtype.ext hfaceNext.symm)
  rcases hvertexCases with hvertexBase | hvertexOpposite
  · left
    have hdarts : outgoingDart = RS.phi beforeDart := by
      exact faceCycleDart_successor_of_modEq RS placement.root
        placement.orbit_card before.1 placement.outgoingPosition hbefore
    have houtgoingIncident : outgoingEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      exact ⟨outgoingDart, rfl, hvertexBase.symm⟩
    have hbeforeIncident : beforeEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      refine ⟨RS.alpha beforeDart, RS.edge_alpha beforeDart, ?_⟩
      rw [← RS.vert_phi_eq_vert_alpha beforeDart, ← hdarts, ← hvertexBase]
    have hbeforeBoundary : beforeEdge ∈ orbitFaceBoundary RS center.1 := by
      change faceCycleEdge RS placement.root before.1 ∈
        orbitFaceBoundary RS center.1
      rw [← placement.root_face]
      exact faceCycleEdge_mem RS placement.root before.1
    have hbeforeNe : outgoingEdge ≠ beforeEdge := by
      intro hedge
      apply (mem_placementSidePositions_iff placement before.1).1 before.2 |>.2
      apply faceCycleEdge_injective RS minimal.facesTwoSided placement.root
      exact hedge.symm
    have hpairs := incidentEdges_inter_faceBoundary_eq_pair RS
      minimal.spherical.cubic minimal.facesTwoSided center.1 vertex
      (Finset.mem_inter.2 ⟨houtgoingIncident, houtgoingBoundary⟩)
      (Finset.mem_inter.2 ⟨hbeforeIncident, hbeforeBoundary⟩) hbeforeNe
    have htargetMem : targetEdge ∈
        RS.incidentEdges vertex ∩ orbitFaceBoundary RS center.1 :=
      Finset.mem_inter.2 ⟨htargetIncident, htargetBoundary⟩
    rw [hpairs] at htargetMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at htargetMem
    exact htargetMem.resolve_left htargetNeOutgoing
  · right
    have hdarts : afterDart = RS.phi outgoingDart := by
      exact faceCycleDart_successor_of_modEq RS placement.root
        placement.orbit_card placement.outgoingPosition after.1 hafter
    have houtgoingIncident : outgoingEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      refine ⟨RS.alpha outgoingDart, RS.edge_alpha outgoingDart, ?_⟩
      exact hvertexOpposite.symm
    have hafterIncident : afterEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      refine ⟨afterDart, rfl, ?_⟩
      rw [hdarts, RS.vert_phi_eq_vert_alpha, ← hvertexOpposite]
    have hafterBoundary : afterEdge ∈ orbitFaceBoundary RS center.1 := by
      change faceCycleEdge RS placement.root after.1 ∈
        orbitFaceBoundary RS center.1
      rw [← placement.root_face]
      exact faceCycleEdge_mem RS placement.root after.1
    have hafterNe : outgoingEdge ≠ afterEdge := by
      intro hedge
      apply (mem_placementSidePositions_iff placement after.1).1 after.2 |>.2
      apply faceCycleEdge_injective RS minimal.facesTwoSided placement.root
      exact hedge.symm
    have hpairs := incidentEdges_inter_faceBoundary_eq_pair RS
      minimal.spherical.cubic minimal.facesTwoSided center.1 vertex
      (Finset.mem_inter.2 ⟨houtgoingIncident, houtgoingBoundary⟩)
      (Finset.mem_inter.2 ⟨hafterIncident, hafterBoundary⟩) hafterNe
    have htargetMem : targetEdge ∈
        RS.incidentEdges vertex ∩ orbitFaceBoundary RS center.1 :=
      Finset.mem_inter.2 ⟨htargetIncident, htargetBoundary⟩
    rw [hpairs] at htargetMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at htargetMem
    exact htargetMem.resolve_left htargetNeOutgoing

/-- The closed-map face across a non-rung position of a placed corridor
hexagon.  This is the generic rotation-system object underlying the
source-specific `localPlacementSideFace`: no annular or opened-carrier data is
needed to define it. -/
noncomputable def placementSideFace
    {RS : RotationSystem V G.edgeSet} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
  ⟨dartOrbitFace RS
      (RS.alpha (faceCycleDart RS placement.root position.1)),
    Finset.mem_univ _⟩

/-- The literal face-cycle edge at a side slot belongs to the opposite-dart
face selected by `placementSideFace`. -/
theorem faceCycleEdge_mem_placementSideFace
    {RS : RotationSystem V G.edgeSet} {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    faceCycleEdge RS placement.root position.1 ∈
      orbitFaceBoundary RS (placementSideFace placement position).1 := by
  let dart := faceCycleDart RS placement.root position.1
  change RS.edgeOf dart ∈ orbitFaceBoundary RS
    (dartOrbitFace RS (RS.alpha dart))
  rw [← RS.edge_alpha dart]
  exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)

/-- Two-sidedness separates the opposite-dart side face from the placed
corridor centre. -/
theorem placementSideFace_val_ne_center
    {RS : RotationSystem V G.edgeSet} (htwoSided : OrbitFacesTwoSided RS)
    {corridorLength : Nat}
    {corridor : OrbitHexCorridorSkeleton RS corridorLength}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor hunique interior)
    (position : {position // position ∈ placementSidePositions placement}) :
    (placementSideFace placement position).1 ≠
      (corridor.faceAt interior.center).1 := by
  let dart := faceCycleDart RS placement.root position.1
  intro hsame
  apply htwoSided dart
  calc
    dartOrbitFace RS dart = dartOrbitFace RS placement.root :=
      dartOrbitFace_faceCycleDart RS placement.root position.1
    _ = (corridor.faceAt interior.center).1 := placement.root_face
    _ = dartOrbitFace RS (RS.alpha dart) := hsame.symm

/-- **L1 (closed face-level bounded interaction).** The edge-level flank
classification identifies the common neighbour itself with one of the two
literal side faces.  This is the closed-map statement transported by the
literal-opening layer. -/
theorem commonNeighbor_eq_outgoing_sideFace
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton graphData.toRotationSystem
      corridorLength)
    {interior : CorridorInterior corridorLength}
    (placement : InternalHexRungPlacement corridor
      (pairwiseUniqueSharedInteriorEdges graphData minimal) interior)
    (before after : {position // position ∈ placementSidePositions placement})
    (hbefore : placement.outgoingPosition.val ≡ before.1.val + 1 [MOD 6])
    (hafter : after.1.val ≡ placement.outgoingPosition.val + 1 [MOD 6])
    (face : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)))
    (hleft : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
        (corridor.faceAt interior.center) face)
    (hright : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
        (corridor.faceAt interior.outgoing.right) face) :
    face = placementSideFace placement before ∨
      face = placementSideFace placement after := by
  let RS := graphData.toRotationSystem
  let allFaces : Finset (OrbitFace RS) := Finset.univ
  let hunique := pairwiseUniqueSharedInteriorEdges graphData minimal
  have classify := commonNeighborEdge_eq_outgoing_flank graphData minimal
    corridor placement before after hbefore hafter face hleft hright
  rcases classify with hedge | hedge
  · left
    let center := corridor.faceAt interior.center
    let side := placementSideFace placement before
    let edge := sharedInteriorEdgeOfAdjOfPairwiseUnique
      (orbitFaceBoundary RS) allFaces hunique hleft
    have hedgeCenter : edge ∈ orbitFaceBoundary RS center.1 :=
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
        (orbitFaceBoundary RS) allFaces hunique hleft
    have hedgeFace : edge ∈ orbitFaceBoundary RS face.1 :=
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        (orbitFaceBoundary RS) allFaces hunique hleft
    have hedgeSide : edge ∈ orbitFaceBoundary RS side.1 := by
      change edge = faceCycleEdge RS placement.root before.1 at hedge
      rw [hedge]
      exact faceCycleEdge_mem_placementSideFace placement before
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) allFaces (orbitFace_incidence_le_two RS)
        center.2 face.2 side.2 (fun h => hleft.ne (Subtype.ext h))
        hedgeCenter hedgeFace hedgeSide
    rcases hcases with hsideCenter | hsideFace
    · exact False.elim
        ((placementSideFace_val_ne_center minimal.facesTwoSided placement before)
          hsideCenter)
    · exact Subtype.ext hsideFace.symm
  · right
    let center := corridor.faceAt interior.center
    let side := placementSideFace placement after
    let edge := sharedInteriorEdgeOfAdjOfPairwiseUnique
      (orbitFaceBoundary RS) allFaces hunique hleft
    have hedgeCenter : edge ∈ orbitFaceBoundary RS center.1 :=
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
        (orbitFaceBoundary RS) allFaces hunique hleft
    have hedgeFace : edge ∈ orbitFaceBoundary RS face.1 :=
      sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        (orbitFaceBoundary RS) allFaces hunique hleft
    have hedgeSide : edge ∈ orbitFaceBoundary RS side.1 := by
      change edge = faceCycleEdge RS placement.root after.1 at hedge
      rw [hedge]
      exact faceCycleEdge_mem_placementSideFace placement after
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) allFaces (orbitFace_incidence_le_two RS)
        center.2 face.2 side.2 (fun h => hleft.ne (Subtype.ext h))
        hedgeCenter hedgeFace hedgeSide
    rcases hcases with hsideCenter | hsideFace
    · exact False.elim
        ((placementSideFace_val_ne_center minimal.facesTwoSided placement after)
          hsideCenter)
    · exact Subtype.ext hsideFace.symm

/-- **L1 (closed two-step rail collision).** A common neighbour of corridor
faces two steps apart is either their displayed middle face, or its canonical
edges from both adjacent centres are among the corresponding outgoing flank
pairs.

This combines the four-cycle classification with the two adjacent
dual-triangle classifications.  It is the exact closed-map invariant needed
to handle distance-two intersections in a recursive rail assembly; remote
intersections are already excluded by geodesicity. -/
theorem twoStepCommonNeighbor_eq_middle_or_outgoing_flanks
    (graphData : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample graphData)
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton graphData.toRotationSystem
      corridorLength)
    {leftInterior : CorridorInterior corridorLength}
    (hnext : leftInterior.center.val + 2 < corridorLength)
    (leftPlacement : InternalHexRungPlacement corridor
      (pairwiseUniqueSharedInteriorEdges graphData minimal) leftInterior)
    (middlePlacement : InternalHexRungPlacement corridor
      (pairwiseUniqueSharedInteriorEdges graphData minimal)
      (nextCorridorInterior leftInterior hnext))
    (leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement})
    (middleBefore middleAfter :
      {position // position ∈ placementSidePositions middlePlacement})
    (hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6])
    (hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6])
    (hmiddleBefore : middlePlacement.outgoingPosition.val ≡
      middleBefore.1.val + 1 [MOD 6])
    (hmiddleAfter : middleAfter.1.val ≡
      middlePlacement.outgoingPosition.val + 1 [MOD 6])
    (face : AmbientFace
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem)))
    (hleft : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
        (corridor.faceAt leftInterior.center) face)
    (hright : (interiorDualGraph
      (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
        (corridor.faceAt
          (nextCorridorInterior leftInterior hnext).outgoing.right) face) :
    face = corridor.faceAt (nextCorridorInterior leftInterior hnext).center ∨
      ((sharedInteriorEdgeOfAdjOfPairwiseUnique
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
          (pairwiseUniqueSharedInteriorEdges graphData minimal) hleft =
            graphData.toRotationSystem.edgeOf
              (faceCycleDart graphData.toRotationSystem leftPlacement.root
                leftBefore.1) ∨
        sharedInteriorEdgeOfAdjOfPairwiseUnique
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
          (pairwiseUniqueSharedInteriorEdges graphData minimal) hleft =
            graphData.toRotationSystem.edgeOf
              (faceCycleDart graphData.toRotationSystem leftPlacement.root
                leftAfter.1)) ∧
       ∃ hmiddle : (interiorDualGraph
          (orbitFaceBoundary graphData.toRotationSystem)
          (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
            (corridor.faceAt
              (nextCorridorInterior leftInterior hnext).center) face,
        sharedInteriorEdgeOfAdjOfPairwiseUnique
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
            (pairwiseUniqueSharedInteriorEdges graphData minimal) hmiddle =
              graphData.toRotationSystem.edgeOf
                (faceCycleDart graphData.toRotationSystem
                  middlePlacement.root middleBefore.1) ∨
          sharedInteriorEdgeOfAdjOfPairwiseUnique
            (orbitFaceBoundary graphData.toRotationSystem)
            (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))
            (pairwiseUniqueSharedInteriorEdges graphData minimal) hmiddle =
              graphData.toRotationSystem.edgeOf
                (faceCycleDart graphData.toRotationSystem
                  middlePlacement.root middleAfter.1)) := by
  let middleInterior := nextCorridorInterior leftInterior hnext
  by_cases hmiddleEq : face = corridor.faceAt middleInterior.center
  · exact Or.inl hmiddleEq
  · right
    have hmiddle : (interiorDualGraph
        (orbitFaceBoundary graphData.toRotationSystem)
        (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Adj
          (corridor.faceAt middleInterior.center) face := by
      exact
        GoertzelV24MinimalDualFourCycleClassification.OrbitHexCorridorSkeleton.middle_adj_commonNeighbor_of_two_step
          graphData minimal corridor
        (first := leftInterior.center) (middle := middleInterior.center)
        (last := middleInterior.outgoing.right) rfl rfl face hleft
        hright.symm hmiddleEq
    refine ⟨commonNeighborEdge_eq_outgoing_flank graphData minimal corridor
      leftPlacement leftBefore leftAfter hleftBefore hleftAfter face hleft
      hmiddle, ?_⟩
    exact ⟨hmiddle,
      commonNeighborEdge_eq_outgoing_flank graphData minimal corridor
        middlePlacement middleBefore middleAfter hmiddleBefore hmiddleAfter
        face hmiddle hright⟩

end

end GoertzelV24MinimalCorridorCommonNeighbors

end Mettapedia.GraphTheory.FourColor
