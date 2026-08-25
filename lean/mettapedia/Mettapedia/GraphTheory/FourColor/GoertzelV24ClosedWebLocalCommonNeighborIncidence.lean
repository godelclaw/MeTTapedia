import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalRailAppend
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSelectedLocalRailAppend
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpace

/-!
# Local common-neighbour incidence on the literal Cell-3 carrier

The closed minimal-counterexample theorem says that the three primal edges
crossed by a facial-dual triangle meet at one ambient vertex.  This file
isolates the strictly local part of transporting that statement to the
cut-open Cell-3 carrier.

The open carrier is not globally cubic or globally two-sided.  Nevertheless,
the displayed corridor face is an annular-interior face, so its boundary is
edge-simple and both endpoints of its outgoing rung are locally cubic.  Hence,
if the outgoing rung and the canonical edge to a common neighbour still meet
at one vertex after opening, that target edge must be one of the two literal
flanks.  This discharges `CommonNeighborEdgesExact`, and therefore
`CommonNeighborsExact`.

The incidence premise below is intentionally not presented as a construction.
The remaining source-formation theorem must obtain it by transporting the
closed minimal-counterexample triangle through the actual annular opening.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorInterfaceMatching
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24HexSlabSideAdjacency
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrientedHexSlab
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

namespace Instance

namespace LocalLayerFormation

namespace SourceLocalRailSuccessor

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique leftInterior}
    {leftBefore leftAfter :
      {position // position ∈ placementSidePositions leftPlacement}}
    {hleftBefore : leftPlacement.outgoingPosition.val ≡
      leftBefore.1.val + 1 [MOD 6]}
    {hleftAfter : leftAfter.1.val ≡
      leftPlacement.outgoingPosition.val + 1 [MOD 6]}
    {rightPlacement : InternalHexRungPlacement
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
      hunique (nextCorridorInterior leftInterior hnext)}

/-- The exact incidence datum left by transporting the closed
minimal-counterexample dual triangle into the literal opening: for every
common neighbour, the outgoing rung and the canonical edge from the left
centre to that neighbour retain a common endpoint.

This is weaker and more geometric than `CommonNeighborEdgesExact`; it neither
names a flank nor classifies the common neighbour. -/
def CommonNeighborVertexIncidence
    (_successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement) : Prop :=
  ∀ (face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
      (hleft : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) face)
      (_hright : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt
              (nextCorridorInterior leftInterior hnext).center) face),
    ∃ vertex : V,
      vertex ∈ web.annular.RS.endpoints
        (web.annular.RS.edgeOf (faceCycleDart web.annular.RS
          leftPlacement.root leftPlacement.outgoingPosition)) ∧
      vertex ∈ web.annular.RS.endpoints
        (sharedInteriorEdgeOfAdjOfPairwiseUnique
          (orbitFaceBoundary web.annular.RS)
          (Finset.univ : Finset (OrbitFace web.annular.RS)) hunique hleft)

/-- Face-local replacement for global two-sidedness in the standard toggle
parity proof.  Injectivity only needs the opposite side of darts on this one
facial orbit to be different. -/
theorem togglesOn_card_eq_incidentEdges_inter_faceEdges_of_localTwoSided
    {W E : Type*} [Fintype W] [DecidableEq W]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem W E) (representative : RS.D) (vertex : W)
    (htwoSided : ∀ dart ∈ RS.faceOrbit representative,
      dartOrbitFace RS dart ≠ dartOrbitFace RS (RS.alpha dart)) :
    (RS.togglesOn vertex representative).card =
      (RS.incidentEdges vertex ∩ RS.faceEdges representative).card := by
  classical
  refine Finset.card_bij (fun dart _ => RS.edgeOf dart) ?_ ?_ ?_
  · intro dart hdart
    rcases (RS.mem_togglesOn_iff).1 hdart with ⟨horbit, htoggle⟩
    have hedgeFace : RS.edgeOf dart ∈ RS.faceEdges representative :=
      (RS.mem_faceEdges_iff).2 ⟨dart, horbit, rfl⟩
    have hvertex :
        (RS.vertOf dart = vertex ∧ RS.vertOf (RS.phi dart) ≠ vertex) ∨
          (RS.vertOf dart ≠ vertex ∧ RS.vertOf (RS.phi dart) = vertex) := by
      by_cases hleft : RS.vertOf dart = vertex
      · by_cases hrightRaw : RS.vertOf (RS.rho (RS.alpha dart)) = vertex
        · exact (htoggle (by
            simp [RotationSystem.phi_apply, hleft, hrightRaw])).elim
        · have hright : RS.vertOf (RS.phi dart) ≠ vertex := by
            intro h
            exact hrightRaw (by simpa [RotationSystem.phi_apply] using h)
          exact Or.inl ⟨hleft, hright⟩
      · by_cases hrightRaw : RS.vertOf (RS.rho (RS.alpha dart)) = vertex
        · have hright : RS.vertOf (RS.phi dart) = vertex := by
            simpa [RotationSystem.phi_apply] using hrightRaw
          exact Or.inr ⟨hleft, hright⟩
        · exact (htoggle (by
            simp [RotationSystem.phi_apply, hleft, hrightRaw])).elim
    have hedgeIncident : RS.edgeOf dart ∈ RS.incidentEdges vertex := by
      rcases hvertex with ⟨hleft, _⟩ | ⟨_, hright⟩
      · exact (RS.mem_incidentEdges_iff).2 ⟨dart, rfl, hleft⟩
      · exact (RS.mem_incidentEdges_iff).2
          ⟨RS.alpha dart, RS.edge_alpha dart,
            (RS.vert_phi_eq_vert_alpha dart).symm.trans hright⟩
    exact Finset.mem_inter.2 ⟨hedgeIncident, hedgeFace⟩
  · intro left hleft right hright hedge
    have hleftOrbit := (RS.mem_togglesOn_iff).1 hleft |>.1
    have hrightOrbit := (RS.mem_togglesOn_iff).1 hright |>.1
    rcases RS.edge_fiber_two_cases
        (e := RS.edgeOf left) (d := left) (y := right)
        rfl (by simpa using hedge.symm) with heq | heq
    · exact heq.symm
    · exfalso
      apply htwoSided left hleftOrbit
      have hleftFace :
          dartOrbitFace RS left = dartOrbitFace RS representative := by
        apply Quotient.sound
        exact ((RS.mem_faceOrbit).1 hleftOrbit).symm
      have hrightFace :
          dartOrbitFace RS right = dartOrbitFace RS representative := by
        apply Quotient.sound
        exact ((RS.mem_faceOrbit).1 hrightOrbit).symm
      rw [← heq]
      exact hleftFace.trans hrightFace.symm
  · intro edge hedge
    have hedgeIncident : edge ∈ RS.incidentEdges vertex :=
      (Finset.mem_inter.1 hedge).1
    have hedgeFace : edge ∈ RS.faceEdges representative :=
      (Finset.mem_inter.1 hedge).2
    rcases (RS.mem_faceEdges_iff).1 hedgeFace with
      ⟨faceDart, hfaceOrbit, hfaceEdge⟩
    rcases (RS.mem_incidentEdges_iff).1 hedgeIncident with
      ⟨vertexDart, hvertexEdge, hvertex⟩
    rcases RS.edge_fiber_two_cases
        (e := RS.edgeOf faceDart) (d := faceDart) (y := vertexDart)
        rfl (by rw [hfaceEdge, ← hvertexEdge]) with heq | heq
    · have hleft : RS.vertOf faceDart = vertex := by
        rw [← heq]
        exact hvertex
      have hright : RS.vertOf (RS.phi faceDart) ≠ vertex := by
        intro hright
        have hvalpha : RS.vertOf (RS.alpha faceDart) = vertex := by
          rw [← RS.vert_phi_eq_vert_alpha faceDart]
          exact hright
        exact RS.no_self_loops faceDart (hleft.trans hvalpha.symm)
      have hrightRaw : RS.vertOf (RS.rho (RS.alpha faceDart)) ≠ vertex := by
        intro h
        exact hright (by simpa [RotationSystem.phi_apply] using h)
      refine ⟨faceDart, (RS.mem_togglesOn_iff).2 ⟨hfaceOrbit, ?_⟩,
        hfaceEdge⟩
      simp [RotationSystem.phi_apply, hleft, hrightRaw]
    · have hright : RS.vertOf (RS.alpha faceDart) = vertex := by
        rw [← heq]
        exact hvertex
      have hleft : RS.vertOf faceDart ≠ vertex := by
        intro hleft
        exact RS.no_self_loops faceDart (hleft.trans hright.symm)
      have hphi : RS.vertOf (RS.phi faceDart) = vertex :=
        (RS.vert_phi_eq_vert_alpha faceDart).trans hright
      have hphiRaw : RS.vertOf (RS.rho (RS.alpha faceDart)) = vertex := by
        simpa [RotationSystem.phi_apply] using hphi
      refine ⟨faceDart, (RS.mem_togglesOn_iff).2 ⟨hfaceOrbit, ?_⟩,
        hfaceEdge⟩
      simp [RotationSystem.phi_apply, hleft, hphiRaw]

/-- At a locally cubic vertex, two distinct edges on a locally two-sided face
exhaust the incident boundary edges. -/
theorem incidentEdges_inter_faceBoundary_eq_pair_of_local
    (RS : RotationSystem V G.edgeSet) (face : OrbitFace RS) (vertex : V)
    {first second : G.edgeSet}
    (hcardThree : (RS.incidentEdges vertex).card = 3)
    (heven : Even ((RS.incidentEdges vertex ∩ orbitFaceBoundary RS face).card))
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
      _ = 3 := hcardThree
  have hcard : incidentFace.card = 2 := by
    change Even incidentFace.card at heven
    rcases heven with ⟨half, hhalf⟩
    omega
  exact Finset.Subset.antisymm
    (by
      intro edge hedge
      have hpairCard : ({first, second} : Finset G.edgeSet).card = 2 :=
        Finset.card_pair hne
      have heq : ({first, second} : Finset G.edgeSet) = incidentFace :=
        Finset.eq_of_subset_of_card_le hpairSubset (by rw [hpairCard, hcard])
      rw [heq]
      exact hedge)
    hpairSubset

/-- **Local rail incidence-to-flank bridge (not Fable flag L1).** The common-vertex incidence
left by the closed minimal-counterexample classification is sufficient on the
literal open carrier: local cubicity and the simple interior face boundary
force the target edge to be one of the two named flanks. -/
theorem commonNeighborEdgesExact_of_commonNeighborVertexIncidence
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hincidence : successor.CommonNeighborVertexIncidence) :
    successor.CommonNeighborEdgesExact := by
  intro face hleft hright
  let RS := web.annular.RS
  let allFaces : Finset (OrbitFace RS) := Finset.univ
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let center := skeleton.faceAt leftInterior.center
  let next := skeleton.faceAt
      (nextCorridorInterior leftInterior hnext).center
  let outgoingDart := faceCycleDart RS leftPlacement.root
    leftPlacement.outgoingPosition
  let beforeDart := faceCycleDart RS leftPlacement.root leftBefore.1
  let afterDart := faceCycleDart RS leftPlacement.root leftAfter.1
  let outgoingEdge := RS.edgeOf outgoingDart
  let beforeEdge := RS.edgeOf beforeDart
  let afterEdge := RS.edgeOf afterDart
  let targetEdge := sharedInteriorEdgeOfAdjOfPairwiseUnique
    (orbitFaceBoundary RS) allFaces hunique hleft
  rcases hincidence face hleft hright with
    ⟨vertex, hvertexOutgoing, hvertexTarget⟩
  have houtgoingFace : dartOrbitFace RS outgoingDart = center.1 := by
    calc
      dartOrbitFace RS outgoingDart =
          dartOrbitFace RS leftPlacement.root :=
        dartOrbitFace_faceCycleDart RS leftPlacement.root
          leftPlacement.outgoingPosition
      _ = center.1 := leftPlacement.root_face
  have hcenterInternal : dartOrbitFace RS outgoingDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [houtgoingFace]
    exact corridor.face_internal leftInterior.center
  have houtgoingOn : outgoingDart ∈ RS.dartsOn outgoingEdge :=
    (RS.mem_dartsOn).2 rfl
  have hvertexCases : vertex = RS.vertOf outgoingDart ∨
      vertex = RS.vertOf (RS.alpha outgoingDart) := by
    rw [RS.endpoints_eq_pair_of_mem houtgoingOn] at hvertexOutgoing
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hvertexOutgoing
  have htargetIncident : targetEdge ∈ RS.incidentEdges vertex :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hvertexTarget
  have htargetBoundary : targetEdge ∈ orbitFaceBoundary RS center.1 :=
    sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_left
      (orbitFaceBoundary RS) allFaces hunique hleft
  have houtgoingBoundary : outgoingEdge ∈ orbitFaceBoundary RS center.1 := by
    change faceCycleEdge RS leftPlacement.root
      leftPlacement.outgoingPosition ∈ orbitFaceBoundary RS center.1
    rw [← leftPlacement.root_face]
    exact faceCycleEdge_mem RS leftPlacement.root leftPlacement.outgoingPosition
  have hfirstSecond :
      (interiorDualGraph (orbitFaceBoundary RS) allFaces).Adj center next := by
    exact skeleton.consecutive_adjacent leftInterior.center
      (nextCorridorInterior leftInterior hnext).center rfl
  have htargetNeOutgoing : targetEdge ≠ outgoingEdge := by
    intro hedge
    have htargetFace : outgoingEdge ∈ orbitFaceBoundary RS face.1 := by
      rw [← hedge]
      exact sharedInteriorEdgeOfAdjOfPairwiseUnique_mem_faceBoundary_right
        (orbitFaceBoundary RS) allFaces hunique hleft
    have hnextFace : outgoingEdge ∈ orbitFaceBoundary RS next.1 := by
      change faceCycleEdge RS leftPlacement.root
        leftPlacement.outgoingPosition ∈ orbitFaceBoundary RS next.1
      rw [leftPlacement.outgoing_edge]
      simpa [next, nextCorridorInterior] using
        skeleton.rungEdge_mem_right hunique leftInterior.outgoing
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) allFaces (orbitFace_incidence_le_two RS)
        center.2 next.2 face.2 (fun h => hfirstSecond.ne (Subtype.ext h))
        houtgoingBoundary hnextFace htargetFace
    rcases hcases with hfaceCenter | hfaceNext
    · exact hleft.ne (Subtype.ext hfaceCenter.symm)
    · exact hright.ne (Subtype.ext hfaceNext.symm)
  have hlocalTwoSided : ∀ dart ∈ RS.faceOrbit leftPlacement.root,
      dartOrbitFace RS dart ≠ dartOrbitFace RS (RS.alpha dart) := by
    intro dart hdart
    apply InteriorFace.dartOrbitFace_ne_alpha web dart
    have hsame : dartOrbitFace RS dart = dartOrbitFace RS leftPlacement.root := by
      apply Quotient.sound
      exact ((RS.mem_faceOrbit).1 hdart).symm
    rw [hsame, leftPlacement.root_face]
    exact corridor.face_internal leftInterior.center
  have heven (candidate : V) :
      Even ((RS.incidentEdges candidate ∩ orbitFaceBoundary RS center.1).card) := by
    have htoggles :=
      togglesOn_card_eq_incidentEdges_inter_faceEdges_of_localTwoSided
        RS leftPlacement.root candidate hlocalTwoSided
    rw [← leftPlacement.root_face,
      orbitFaceBoundary_dartOrbitFace_eq_faceEdges]
    rw [← htoggles]
    exact RS.togglesOn_card_even leftPlacement.root candidate
  rcases hvertexCases with hvertexBase | hvertexOpposite
  · left
    have hdarts : outgoingDart = RS.phi beforeDart :=
      faceCycleDart_successor_of_modEq RS leftPlacement.root
        leftPlacement.orbit_card leftBefore.1 leftPlacement.outgoingPosition
        hleftBefore
    have houtgoingIncident : outgoingEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      exact ⟨outgoingDart, rfl, hvertexBase.symm⟩
    have hbeforeIncident : beforeEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      refine ⟨RS.alpha beforeDart, RS.edge_alpha beforeDart, ?_⟩
      rw [← RS.vert_phi_eq_vert_alpha beforeDart, ← hdarts, ← hvertexBase]
    have hbeforeBoundary : beforeEdge ∈ orbitFaceBoundary RS center.1 := by
      change faceCycleEdge RS leftPlacement.root leftBefore.1 ∈
        orbitFaceBoundary RS center.1
      rw [← leftPlacement.root_face]
      exact faceCycleEdge_mem RS leftPlacement.root leftBefore.1
    have hbeforeNe : outgoingEdge ≠ beforeEdge := by
      intro hedge
      apply (mem_placementSidePositions_iff leftPlacement leftBefore.1).1
        leftBefore.2 |>.2
      apply InteriorFace.faceCycleEdge_injective web leftPlacement.root
        (by simpa [leftPlacement.root_face] using
          corridor.face_internal leftInterior.center)
      exact hedge.symm
    have hcardThree : (RS.incidentEdges vertex).card = 3 := by
      rw [hvertexBase]
      rw [RS.incidentEdges_card_eq_dartsAt_card]
      exact InteriorFace.dartsAt_card_eq_three web hcenterInternal
    have hpairs := incidentEdges_inter_faceBoundary_eq_pair_of_local RS
      center.1 vertex hcardThree (heven vertex)
      (Finset.mem_inter.2 ⟨houtgoingIncident, houtgoingBoundary⟩)
      (Finset.mem_inter.2 ⟨hbeforeIncident, hbeforeBoundary⟩) hbeforeNe
    have htargetMem : targetEdge ∈
        RS.incidentEdges vertex ∩ orbitFaceBoundary RS center.1 :=
      Finset.mem_inter.2 ⟨htargetIncident, htargetBoundary⟩
    rw [hpairs] at htargetMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at htargetMem
    exact htargetMem.resolve_left htargetNeOutgoing
  · right
    have hdarts : afterDart = RS.phi outgoingDart :=
      faceCycleDart_successor_of_modEq RS leftPlacement.root
        leftPlacement.orbit_card leftPlacement.outgoingPosition leftAfter.1
        hleftAfter
    have houtgoingIncident : outgoingEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      exact ⟨RS.alpha outgoingDart, RS.edge_alpha outgoingDart,
        hvertexOpposite.symm⟩
    have hafterIncident : afterEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      refine ⟨afterDart, rfl, ?_⟩
      rw [hdarts, RS.vert_phi_eq_vert_alpha, ← hvertexOpposite]
    have hafterBoundary : afterEdge ∈ orbitFaceBoundary RS center.1 := by
      change faceCycleEdge RS leftPlacement.root leftAfter.1 ∈
        orbitFaceBoundary RS center.1
      rw [← leftPlacement.root_face]
      exact faceCycleEdge_mem RS leftPlacement.root leftAfter.1
    have hafterNe : outgoingEdge ≠ afterEdge := by
      intro hedge
      apply (mem_placementSidePositions_iff leftPlacement leftAfter.1).1
        leftAfter.2 |>.2
      apply InteriorFace.faceCycleEdge_injective web leftPlacement.root
        (by simpa [leftPlacement.root_face] using
          corridor.face_internal leftInterior.center)
      exact hedge.symm
    have hnextFace : dartOrbitFace RS (RS.alpha outgoingDart) = next.1 := by
      apply InteriorFace.alpha_face_eq_of_mem_other web outgoingDart
        hcenterInternal next.1
      · change faceCycleEdge RS leftPlacement.root
          leftPlacement.outgoingPosition ∈ orbitFaceBoundary RS next.1
        rw [leftPlacement.outgoing_edge]
        simpa [next, nextCorridorInterior] using
          skeleton.rungEdge_mem_right hunique leftInterior.outgoing
      · intro hsame
        have hindices := skeleton.faceAt_injective (Subtype.ext
          (houtgoingFace.symm.trans hsame))
        have hvalues := congrArg Fin.val hindices
        simp [nextCorridorInterior] at hvalues
    have hnextInternal : dartOrbitFace RS (RS.alpha outgoingDart) ∈
        web.annular.cellulation.interiorFaces := by
      rw [hnextFace]
      exact corridor.face_internal
        (nextCorridorInterior leftInterior hnext).center
    have hcardThree : (RS.incidentEdges vertex).card = 3 := by
      rw [hvertexOpposite]
      rw [RS.incidentEdges_card_eq_dartsAt_card]
      exact InteriorFace.dartsAt_card_eq_three web hnextInternal
    have hpairs := incidentEdges_inter_faceBoundary_eq_pair_of_local RS
      center.1 vertex hcardThree (heven vertex)
      (Finset.mem_inter.2 ⟨houtgoingIncident, houtgoingBoundary⟩)
      (Finset.mem_inter.2 ⟨hafterIncident, hafterBoundary⟩) hafterNe
    have htargetMem : targetEdge ∈
        RS.incidentEdges vertex ∩ orbitFaceBoundary RS center.1 :=
      Finset.mem_inter.2 ⟨htargetIncident, htargetBoundary⟩
    rw [hpairs] at htargetMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at htargetMem
    exact htargetMem.resolve_left htargetNeOutgoing

/-- The transported common-vertex incidence also discharges the face-level
statement consumed by literal rail append. -/
theorem commonNeighborsExact_of_commonNeighborVertexIncidence
    (successor : SourceLocalRailSuccessor hnext leftPlacement leftBefore
      leftAfter hleftBefore hleftAfter rightPlacement)
    (hincidence : successor.CommonNeighborVertexIncidence) :
    successor.CommonNeighborsExact :=
  (successor.commonNeighborsExact_iff_commonNeighborEdgesExact).2
    (successor.commonNeighborEdgesExact_of_commonNeighborVertexIncidence
      hincidence)

end SourceLocalRailSuccessor

end LocalLayerFormation

namespace SelectedLocalLayerFormation

namespace SeparatedSelectedSourceLocalRailSuccessor

variable
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    {corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength}
    {rungs : SelectedCorridorRungs
      corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton}
    {leftInterior : CorridorInterior blockLength}
    {hnext : leftInterior.center.val + 2 < blockLength}
    {leftPlacement : SelectedInternalHexRungPlacement corridor rungs leftInterior}
    {rightPlacement : SelectedInternalHexRungPlacement corridor rungs
      (nextCorridorInterior leftInterior hnext)}

/-- Pointwise selected-carrier incidence at one common dual neighbour.  One
literal edge shared with the left corridor face retains a common endpoint
with the selected outgoing rung. -/
def CommonNeighborVertexIncidenceAt
    (_successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (_hleft : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) face)
    (_hright : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt
              (nextCorridorInterior leftInterior hnext).center) face) : Prop :=
  ∃ targetEdge : G.edgeSet,
      targetEdge ∈ orbitFaceBoundary web.annular.RS
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center).1 ∧
      targetEdge ∈ orbitFaceBoundary web.annular.RS face.1 ∧
      ∃ vertex : V,
        vertex ∈ web.annular.RS.endpoints
          (web.annular.RS.edgeOf (faceCycleDart web.annular.RS
            leftPlacement.root leftPlacement.outgoingPosition)) ∧
        vertex ∈ web.annular.RS.endpoints targetEdge

/-- The selected-carrier form of the closed dual-triangle incidence datum at
every common neighbour.  No uniqueness of the shared edge is asserted. -/
def CommonNeighborVertexIncidence
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement) : Prop :=
  ∀ (face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
      (hleft : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) face)
      (hright : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
        (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
          ((corridor.toCleanOrbitHexCorridorSkeleton
            |>.toOrbitHexCorridorSkeleton).faceAt
              (nextCorridorInterior leftInterior hnext).center) face),
    successor.CommonNeighborVertexIncidenceAt face hleft hright

private theorem face_eq_selectedPlacementSideFace_of_edge_eq
    (face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hleft : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) face)
    (targetEdge : G.edgeSet)
    (htargetCenter : targetEdge ∈ orbitFaceBoundary web.annular.RS
      ((corridor.toCleanOrbitHexCorridorSkeleton
        |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center).1)
    (htargetFace : targetEdge ∈ orbitFaceBoundary web.annular.RS face.1)
    (position : {position // position ∈
      selectedPlacementSidePositions leftPlacement})
    (hedge : targetEdge = web.annular.RS.edgeOf
      (faceCycleDart web.annular.RS leftPlacement.root position.1)) :
    face = selectedPlacementSideFace leftPlacement position := by
  let center := (corridor.toCleanOrbitHexCorridorSkeleton
    |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center
  let side := selectedPlacementSideFace leftPlacement position
  let sideEdge := web.annular.RS.edgeOf
    (faceCycleDart web.annular.RS leftPlacement.root position.1)
  have hedgeCenter : sideEdge ∈ orbitFaceBoundary web.annular.RS center.1 := by
    dsimp only [sideEdge]
    rw [← hedge]
    exact htargetCenter
  have hedgeFace : sideEdge ∈ orbitFaceBoundary web.annular.RS face.1 := by
    dsimp only [sideEdge]
    rw [← hedge]
    exact htargetFace
  have hedgeSide : sideEdge ∈ orbitFaceBoundary web.annular.RS side.1 := by
    change web.annular.RS.edgeOf
      (faceCycleDart web.annular.RS leftPlacement.root position.1) ∈
        orbitFaceBoundary web.annular.RS
          (dartOrbitFace web.annular.RS
            (web.annular.RS.alpha
              (faceCycleDart web.annular.RS leftPlacement.root position.1)))
    rw [← web.annular.RS.edge_alpha]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace web.annular.RS _
  have hcases :=
    eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))
      (orbitFace_incidence_le_two web.annular.RS)
      center.2 face.2 side.2 (fun h => hleft.ne (Subtype.ext h))
      hedgeCenter hedgeFace hedgeSide
  rcases hcases with hsideCenter | hsideFace
  · exact False.elim
      ((selectedPlacementSideFace_val_ne_center (corridor := corridor)
        leftPlacement position) hsideCenter)
  · exact Subtype.ext hsideFace.symm

/-- **Pointwise selected incidence-to-flank bridge.** Literal common-endpoint
incidence at one common neighbour puts that face on one of the two named
flanks of the outgoing rung.

The proof uses only local cubicity and local two-sidedness of the displayed
interior face.  In particular it does not restore the false global
pairwise-unique shared-edge premise on the opened annulus. -/
theorem face_eq_before_or_after_of_commonNeighborVertexIncidenceAt
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (face : AmbientFace (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (hleft : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt leftInterior.center) face)
    (hright : (interiorDualGraph (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS))).Adj
        ((corridor.toCleanOrbitHexCorridorSkeleton
          |>.toOrbitHexCorridorSkeleton).faceAt
            (nextCorridorInterior leftInterior hnext).center) face)
    (hincidence : successor.CommonNeighborVertexIncidenceAt face hleft hright) :
    face = selectedPlacementSideFace leftPlacement successor.frame.leftBefore ∨
      face = selectedPlacementSideFace leftPlacement successor.frame.leftAfter := by
  let RS := web.annular.RS
  let skeleton := corridor.toCleanOrbitHexCorridorSkeleton.toOrbitHexCorridorSkeleton
  let center := skeleton.faceAt leftInterior.center
  let next := skeleton.faceAt
    (nextCorridorInterior leftInterior hnext).center
  let outgoingDart := faceCycleDart RS leftPlacement.root
    leftPlacement.outgoingPosition
  let beforeDart := faceCycleDart RS leftPlacement.root
    successor.frame.leftBefore.1
  let afterDart := faceCycleDart RS leftPlacement.root
    successor.frame.leftAfter.1
  let outgoingEdge := RS.edgeOf outgoingDart
  let beforeEdge := RS.edgeOf beforeDart
  let afterEdge := RS.edgeOf afterDart
  rcases hincidence with
    ⟨targetEdge, htargetCenter, htargetFace, vertex,
      hvertexOutgoing, hvertexTarget⟩
  have houtgoingFace : dartOrbitFace RS outgoingDart = center.1 := by
    calc
      dartOrbitFace RS outgoingDart = dartOrbitFace RS leftPlacement.root :=
        dartOrbitFace_faceCycleDart RS leftPlacement.root
          leftPlacement.outgoingPosition
      _ = center.1 := leftPlacement.root_face
  have hcenterInternal : dartOrbitFace RS outgoingDart ∈
      web.annular.cellulation.interiorFaces := by
    rw [houtgoingFace]
    exact corridor.face_internal leftInterior.center
  have houtgoingOn : outgoingDart ∈ RS.dartsOn outgoingEdge :=
    (RS.mem_dartsOn).2 rfl
  have hvertexCases : vertex = RS.vertOf outgoingDart ∨
      vertex = RS.vertOf (RS.alpha outgoingDart) := by
    rw [RS.endpoints_eq_pair_of_mem houtgoingOn] at hvertexOutgoing
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hvertexOutgoing
  have htargetIncident : targetEdge ∈ RS.incidentEdges vertex :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hvertexTarget
  have houtgoingBoundary : outgoingEdge ∈ orbitFaceBoundary RS center.1 := by
    change faceCycleEdge RS leftPlacement.root
      leftPlacement.outgoingPosition ∈ orbitFaceBoundary RS center.1
    rw [← leftPlacement.root_face]
    exact faceCycleEdge_mem RS leftPlacement.root leftPlacement.outgoingPosition
  have hnextFace : dartOrbitFace RS (RS.alpha outgoingDart) = next.1 := by
    simpa [RS, skeleton, outgoingDart, next] using
      selectedOutgoingAlphaFace_eq_nextCenter (corridor := corridor)
        hnext leftPlacement
  have hnextBoundary : outgoingEdge ∈ orbitFaceBoundary RS next.1 := by
    have hraw := edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS
      (RS.alpha outgoingDart)
    rw [RS.edge_alpha, hnextFace] at hraw
    exact hraw
  have hfirstSecond :
      (interiorDualGraph (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).Adj center next := by
    exact skeleton.consecutive_adjacent leftInterior.center
      (nextCorridorInterior leftInterior hnext).center rfl
  have htargetNeOutgoing : targetEdge ≠ outgoingEdge := by
    intro hedge
    have houtgoingFaceTarget : outgoingEdge ∈ orbitFaceBoundary RS face.1 := by
      rw [← hedge]
      exact htargetFace
    have hcases :=
      eq_or_eq_of_mem_faceBoundary_of_mem_faceBoundary_of_mem_faceBoundary_of_ne_of_count_le_two
        (orbitFaceBoundary RS) (Finset.univ : Finset (OrbitFace RS))
        (orbitFace_incidence_le_two RS)
        center.2 next.2 face.2
        (fun h => hfirstSecond.ne (Subtype.ext h))
        houtgoingBoundary hnextBoundary houtgoingFaceTarget
    rcases hcases with hfaceCenter | hfaceNext
    · exact hleft.ne (Subtype.ext hfaceCenter.symm)
    · exact hright.ne (Subtype.ext hfaceNext.symm)
  have hlocalTwoSided : ∀ dart ∈ RS.faceOrbit leftPlacement.root,
      dartOrbitFace RS dart ≠ dartOrbitFace RS (RS.alpha dart) := by
    intro dart hdart
    apply InteriorFace.dartOrbitFace_ne_alpha web dart
    have hsame : dartOrbitFace RS dart =
        dartOrbitFace RS leftPlacement.root := by
      apply Quotient.sound
      exact ((RS.mem_faceOrbit).1 hdart).symm
    rw [hsame, leftPlacement.root_face]
    exact corridor.face_internal leftInterior.center
  have heven (candidate : V) :
      Even ((RS.incidentEdges candidate ∩ orbitFaceBoundary RS center.1).card) := by
    have htoggles :=
      LocalLayerFormation.SourceLocalRailSuccessor.togglesOn_card_eq_incidentEdges_inter_faceEdges_of_localTwoSided
        RS leftPlacement.root candidate hlocalTwoSided
    rw [← leftPlacement.root_face,
      orbitFaceBoundary_dartOrbitFace_eq_faceEdges]
    rw [← htoggles]
    exact RS.togglesOn_card_even leftPlacement.root candidate
  rcases hvertexCases with hvertexBase | hvertexOpposite
  · left
    have hdarts : outgoingDart = RS.phi beforeDart :=
      faceCycleDart_successor_of_modEq RS leftPlacement.root
        leftPlacement.orbit_card successor.frame.leftBefore.1
        leftPlacement.outgoingPosition successor.frame.leftBefore_mod
    have houtgoingIncident : outgoingEdge ∈ RS.incidentEdges vertex := by
      exact (RS.mem_incidentEdges_iff).2
        ⟨outgoingDart, rfl, hvertexBase.symm⟩
    have hbeforeIncident : beforeEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      refine ⟨RS.alpha beforeDart, RS.edge_alpha beforeDart, ?_⟩
      rw [← RS.vert_phi_eq_vert_alpha beforeDart, ← hdarts, ← hvertexBase]
    have hbeforeBoundary : beforeEdge ∈ orbitFaceBoundary RS center.1 := by
      change faceCycleEdge RS leftPlacement.root
        successor.frame.leftBefore.1 ∈ orbitFaceBoundary RS center.1
      rw [← leftPlacement.root_face]
      exact faceCycleEdge_mem RS leftPlacement.root successor.frame.leftBefore.1
    have hbeforeNe : outgoingEdge ≠ beforeEdge := by
      intro hedge
      apply ((mem_selectedPlacementSidePositions_iff leftPlacement
        successor.frame.leftBefore.1).1 successor.frame.leftBefore.2).2
      apply InteriorFace.faceCycleEdge_injective web leftPlacement.root
        (by simpa [leftPlacement.root_face] using
          corridor.face_internal leftInterior.center)
      exact hedge.symm
    have hcardThree : (RS.incidentEdges vertex).card = 3 := by
      rw [hvertexBase, RS.incidentEdges_card_eq_dartsAt_card]
      exact InteriorFace.dartsAt_card_eq_three web hcenterInternal
    have hpairs :=
      LocalLayerFormation.SourceLocalRailSuccessor.incidentEdges_inter_faceBoundary_eq_pair_of_local
        RS center.1 vertex hcardThree (heven vertex)
        (Finset.mem_inter.2 ⟨houtgoingIncident, houtgoingBoundary⟩)
        (Finset.mem_inter.2 ⟨hbeforeIncident, hbeforeBoundary⟩) hbeforeNe
    have htargetMem : targetEdge ∈
        RS.incidentEdges vertex ∩ orbitFaceBoundary RS center.1 :=
      Finset.mem_inter.2 ⟨htargetIncident, htargetCenter⟩
    rw [hpairs] at htargetMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at htargetMem
    exact face_eq_selectedPlacementSideFace_of_edge_eq
      (corridor := corridor) face hleft targetEdge htargetCenter htargetFace
      successor.frame.leftBefore
      (htargetMem.resolve_left htargetNeOutgoing)
  · right
    have hdarts : afterDart = RS.phi outgoingDart :=
      faceCycleDart_successor_of_modEq RS leftPlacement.root
        leftPlacement.orbit_card leftPlacement.outgoingPosition
        successor.frame.leftAfter.1 successor.frame.leftAfter_mod
    have houtgoingIncident : outgoingEdge ∈ RS.incidentEdges vertex := by
      exact (RS.mem_incidentEdges_iff).2
        ⟨RS.alpha outgoingDart, RS.edge_alpha outgoingDart,
          hvertexOpposite.symm⟩
    have hafterIncident : afterEdge ∈ RS.incidentEdges vertex := by
      apply (RS.mem_incidentEdges_iff).2
      refine ⟨afterDart, rfl, ?_⟩
      rw [hdarts, RS.vert_phi_eq_vert_alpha, ← hvertexOpposite]
    have hafterBoundary : afterEdge ∈ orbitFaceBoundary RS center.1 := by
      change faceCycleEdge RS leftPlacement.root
        successor.frame.leftAfter.1 ∈ orbitFaceBoundary RS center.1
      rw [← leftPlacement.root_face]
      exact faceCycleEdge_mem RS leftPlacement.root successor.frame.leftAfter.1
    have hafterNe : outgoingEdge ≠ afterEdge := by
      intro hedge
      apply ((mem_selectedPlacementSidePositions_iff leftPlacement
        successor.frame.leftAfter.1).1 successor.frame.leftAfter.2).2
      apply InteriorFace.faceCycleEdge_injective web leftPlacement.root
        (by simpa [leftPlacement.root_face] using
          corridor.face_internal leftInterior.center)
      exact hedge.symm
    have hnextInternal : dartOrbitFace RS (RS.alpha outgoingDart) ∈
        web.annular.cellulation.interiorFaces := by
      rw [hnextFace]
      exact corridor.face_internal
        (nextCorridorInterior leftInterior hnext).center
    have hcardThree : (RS.incidentEdges vertex).card = 3 := by
      rw [hvertexOpposite, RS.incidentEdges_card_eq_dartsAt_card]
      exact InteriorFace.dartsAt_card_eq_three web hnextInternal
    have hpairs :=
      LocalLayerFormation.SourceLocalRailSuccessor.incidentEdges_inter_faceBoundary_eq_pair_of_local
        RS center.1 vertex hcardThree (heven vertex)
        (Finset.mem_inter.2 ⟨houtgoingIncident, houtgoingBoundary⟩)
        (Finset.mem_inter.2 ⟨hafterIncident, hafterBoundary⟩) hafterNe
    have htargetMem : targetEdge ∈
        RS.incidentEdges vertex ∩ orbitFaceBoundary RS center.1 :=
      Finset.mem_inter.2 ⟨htargetIncident, htargetCenter⟩
    rw [hpairs] at htargetMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at htargetMem
    exact face_eq_selectedPlacementSideFace_of_edge_eq
      (corridor := corridor) face hleft targetEdge htargetCenter htargetFace
      successor.frame.leftAfter
      (htargetMem.resolve_left htargetNeOutgoing)

/-- The pointwise bridge applied at every common neighbour supplies the exact
classification consumed by selected rail append. -/
theorem commonNeighborsExact_of_commonNeighborVertexIncidence
    (successor : SeparatedSelectedSourceLocalRailSuccessor hnext leftPlacement
      rightPlacement)
    (hincidence : successor.CommonNeighborVertexIncidence) :
    successor.CommonNeighborsExact := by
  intro face hleft hright
  exact successor.face_eq_before_or_after_of_commonNeighborVertexIncidenceAt
    face hleft hright (hincidence face hleft hright)

end SeparatedSelectedSourceLocalRailSuccessor

end SelectedLocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
