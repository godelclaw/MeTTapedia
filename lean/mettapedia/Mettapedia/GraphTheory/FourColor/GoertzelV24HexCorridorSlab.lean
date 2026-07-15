import Mettapedia.GraphTheory.FourColor.GoertzelV24CleanHexCorridor

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCorridorSlab

open GoertzelV24CleanHexCorridor
open GoertzelV24CurvatureScope
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexCorridorSkeleton
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceCurvatureBulk
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The four non-rung edges of an internal corridor hexagon. These are the
primal interface through which the corridor slab meets its two sides. -/
def internalSideEdges {RS : RotationSystem V E} {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength) : Finset E :=
  orbitFaceBoundary RS (corridor.faceAt interior.center).1 \
    {corridor.rungEdge hunique interior.incoming,
      corridor.rungEdge hunique interior.outgoing}

@[simp]
theorem mem_internalSideEdges_iff {RS : RotationSystem V E}
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength) (edge : E) :
    edge ∈ internalSideEdges corridor hunique interior ↔
      edge ∈ orbitFaceBoundary RS (corridor.faceAt interior.center).1 ∧
      edge ≠ corridor.rungEdge hunique interior.incoming ∧
      edge ≠ corridor.rungEdge hunique interior.outgoing := by
  simp [internalSideEdges]

/-- Every internal corridor hexagon has exactly four side-interface edges. -/
theorem card_internalSideEdges_eq_four {RS : RotationSystem V E}
    {corridorLength : Nat}
    (corridor : OrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength) :
    (internalSideEdges corridor hunique interior).card = 4 := by
  have hrungsNe : corridor.rungEdge hunique interior.incoming ≠
      corridor.rungEdge hunique interior.outgoing := by
    intro heq
    exact interior.incoming_ne_outgoing
      (corridor.rungEdge_injective htwoSided hunique heq)
  have hsubset :
      ({corridor.rungEdge hunique interior.incoming,
          corridor.rungEdge hunique interior.outgoing} : Finset E) ⊆
        orbitFaceBoundary RS (corridor.faceAt interior.center).1 := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl
    · simpa using corridor.rungEdge_mem_right hunique interior.incoming
    · exact corridor.rungEdge_mem_left hunique interior.outgoing
  rw [internalSideEdges, Finset.card_sdiff_of_subset hsubset,
    corridor.hexagonal]
  simp [hrungsNe]

/-- Incidence data for the unique face on the other side of a facial edge.
The witness is derived from the opposite dart, not stored in the rotation
system. -/
structure OrbitFaceAcrossEdgeWitness (RS : RotationSystem V E)
    (face : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (edge : E) where
  across : AmbientFace (Finset.univ : Finset (OrbitFace RS))
  face_ne_across : face ≠ across
  edge_interior : edge ∈ interiorEdgeSupport (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))
  edge_mem_across : edge ∈ orbitFaceBoundary RS across.1

/-- Two-sidedness computes the face across every edge of a quotient facial
boundary. -/
theorem exists_orbitFaceAcrossEdgeWitness
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (face : AmbientFace (Finset.univ : Finset (OrbitFace RS))) (edge : E)
    (hedge : edge ∈ orbitFaceBoundary RS face.1) :
    Nonempty (OrbitFaceAcrossEdgeWitness RS face edge) := by
  rcases (mem_orbitFaceBoundary_iff RS face.1 edge).1 hedge with
    ⟨dart, hdartFace, hdartEdge⟩
  have hdartOrbitFace : dartOrbitFace RS dart = face.1 :=
    (mem_orbitFaceDarts_iff RS face.1 dart).1 hdartFace
  let across : AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
    ⟨dartOrbitFace RS (RS.alpha dart), by simp⟩
  have hfaceNeAcross : face ≠ across := by
    intro heq
    apply htwoSided dart
    exact hdartOrbitFace.trans (congrArg Subtype.val heq)
  have hedgeAcross : edge ∈ orbitFaceBoundary RS across.1 := by
    change edge ∈ orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart))
    rw [← hdartEdge, ← RS.edge_alpha dart]
    exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)
  have hedgeInterior : edge ∈ interiorEdgeSupport (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) := by
    apply (mem_interiorEdgeSupport_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    exact ⟨Finset.mem_biUnion.2 ⟨face.1, face.2, hedge⟩,
      orbitFace_totalIncidenceCount_eq_two_of_twoSided RS htwoSided edge⟩
  exact ⟨⟨across, hfaceNeAcross, hedgeInterior, hedgeAcross⟩⟩

/-- Canonical choice of the opposite quotient face across a facial edge. -/
noncomputable def orbitFaceAcrossEdgeWitness
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (face : AmbientFace (Finset.univ : Finset (OrbitFace RS))) (edge : E)
    (hedge : edge ∈ orbitFaceBoundary RS face.1) :
    OrbitFaceAcrossEdgeWitness RS face edge :=
  Classical.choice
    (exists_orbitFaceAcrossEdgeWitness RS htwoSided face edge hedge)

namespace OrbitFaceAcrossEdgeWitness

theorem adjacent {RS : RotationSystem V E}
    {face : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {edge : E} (witness : OrbitFaceAcrossEdgeWitness RS face edge)
    (hedge : edge ∈ orbitFaceBoundary RS face.1) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj face witness.across := by
  apply (interiorDualGraph_adj_iff (orbitFaceBoundary RS)
    (Finset.univ : Finset (OrbitFace RS))).2
  exact ⟨fun heq => witness.face_ne_across (Subtype.ext heq),
    edge, witness.edge_interior, hedge, witness.edge_mem_across⟩

end OrbitFaceAcrossEdgeWitness

/-- The selected face across a side-interface edge of an internal clean
corridor hexagon. -/
noncomputable def internalSideNeighbor {RS : RotationSystem V E}
    {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength)
    (side : {edge // edge ∈ internalSideEdges
      clean.toOrbitHexCorridorSkeleton hunique interior}) :
    AmbientFace (Finset.univ : Finset (OrbitFace RS)) :=
  (orbitFaceAcrossEdgeWitness RS htwoSided
    (clean.toOrbitHexCorridorSkeleton.faceAt interior.center) side.1
    ((mem_internalSideEdges_iff clean.toOrbitHexCorridorSkeleton
      hunique interior side.1).1 side.2).1).across

theorem internalSideNeighbor_adjacent {RS : RotationSystem V E}
    {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength)
    (side : {edge // edge ∈ internalSideEdges
      clean.toOrbitHexCorridorSkeleton hunique interior}) :
    (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        (clean.toOrbitHexCorridorSkeleton.faceAt interior.center)
        (internalSideNeighbor clean htwoSided hunique interior side) := by
  exact (orbitFaceAcrossEdgeWitness RS htwoSided
    (clean.toOrbitHexCorridorSkeleton.faceAt interior.center) side.1
    ((mem_internalSideEdges_iff clean.toOrbitHexCorridorSkeleton
      hunique interior side.1).1 side.2).1).adjacent
        ((mem_internalSideEdges_iff clean.toOrbitHexCorridorSkeleton
          hunique interior side.1).1 side.2).1

/-- Every side face in the extracted radius-one slab is hexagonal. -/
theorem internalSideNeighbor_hexagonal {RS : RotationSystem V E}
    {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength)
    (side : {edge // edge ∈ internalSideEdges
      clean.toOrbitHexCorridorSkeleton hunique interior}) :
    (orbitFaceBoundary RS
      (internalSideNeighbor clean htwoSided hunique interior side).1).card = 6 :=
  clean.neighbor_hexagonal interior.center _
    (internalSideNeighbor_adjacent clean htwoSided hunique interior side)

/-- A side-interface edge cannot lead back to any face of the corridor. For
nonconsecutive indices this is geodesic inducedness; at the predecessor and
successor it is the uniqueness of the canonical rung. -/
theorem internalSideNeighbor_ne_faceAt {RS : RotationSystem V E}
    {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength)
    (side : {edge // edge ∈ internalSideEdges
      clean.toOrbitHexCorridorSkeleton hunique interior})
    (index : Fin corridorLength) :
    internalSideNeighbor clean htwoSided hunique interior side ≠
      clean.toOrbitHexCorridorSkeleton.faceAt index := by
  let corridor := clean.toOrbitHexCorridorSkeleton
  let center := corridor.faceAt interior.center
  have hside :=
    (mem_internalSideEdges_iff corridor hunique interior side.1).1 side.2
  have hsideBoundary : side.1 ∈ orbitFaceBoundary RS center.1 := hside.1
  let witness := orbitFaceAcrossEdgeWitness RS htwoSided center side.1
    hsideBoundary
  have hedgeNeighbor : side.1 ∈ orbitFaceBoundary RS
      (internalSideNeighbor clean htwoSided hunique interior side).1 := by
    exact witness.edge_mem_across
  have hedgeInterior : side.1 ∈ interiorEdgeSupport (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) := witness.edge_interior
  have hadj := internalSideNeighbor_adjacent clean htwoSided hunique interior side
  intro hneighbor
  have hadjIndex : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Adj
        center (corridor.faceAt index) := by
    simpa [center, corridor, hneighbor] using hadj
  have hedgeIndex : side.1 ∈
      orbitFaceBoundary RS (corridor.faceAt index).1 := by
    simpa [corridor, hneighbor] using hedgeNeighbor
  have hindexValNe : index.val ≠ interior.center.val := by
    intro hval
    have hindex : index = interior.center := Fin.ext hval
    subst index
    exact hadjIndex.ne rfl
  rcases Nat.lt_or_gt_of_ne hindexValNe with hbefore | hafter
  · have hnotSeparated : ¬ index.val + 1 < interior.center.val := by
      intro hseparated
      exact (corridor.separated_not_adjacent index interior.center hseparated)
        hadjIndex.symm
    have hpredecessorVal : interior.center.val = index.val + 1 := by omega
    have hpredecessor : index = interior.incoming.left := by
      apply Fin.ext
      change index.val = interior.center.val - 1
      have hcenterPositive := interior.center_pos
      omega
    have hshared : side.1 ∈ sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (corridor.faceAt interior.incoming.left).1
        (corridor.faceAt interior.incoming.right).1 := by
      apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).2
      refine ⟨hedgeInterior, ?_, ?_⟩
      · simpa [hpredecessor] using hedgeIndex
      · simpa using hsideBoundary
    have hrung := corridor.rungEdge_eq_of_shared hunique interior.incoming hshared
    exact hside.2.1 hrung.symm
  · have hnotSeparated : ¬ interior.center.val + 1 < index.val := by
      intro hseparated
      exact (corridor.separated_not_adjacent interior.center index hseparated)
        hadjIndex
    have hsuccessorVal : index.val = interior.center.val + 1 := by omega
    have hsuccessor : index = interior.outgoing.right := by
      apply Fin.ext
      exact hsuccessorVal
    have hshared : side.1 ∈ sharedInteriorEdges (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))
        (corridor.faceAt interior.outgoing.left).1
        (corridor.faceAt interior.outgoing.right).1 := by
      apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).2
      refine ⟨hedgeInterior, ?_, ?_⟩
      · simpa using hsideBoundary
      · simpa [hsuccessor] using hedgeIndex
    have hrung := corridor.rungEdge_eq_of_shared hunique interior.outgoing hshared
    exact hside.2.2 hrung.symm

/-- Pairwise edge-simple face incidence makes the four side-neighbor faces
distinct. Thus an internal clean corridor hexagon has a genuine width-four
external facial interface, rather than four edge labels that may collapse. -/
theorem internalSideNeighbor_injective {RS : RotationSystem V E}
    {corridorLength : Nat}
    (clean : CleanOrbitHexCorridorSkeleton RS corridorLength)
    (htwoSided : OrbitFacesTwoSided RS)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)))
    (interior : CorridorInterior corridorLength) :
    Function.Injective
      (internalSideNeighbor clean htwoSided hunique interior) := by
  intro left right hfaces
  apply Subtype.ext
  let corridor := clean.toOrbitHexCorridorSkeleton
  let center := corridor.faceAt interior.center
  have hleftBoundary :=
    ((mem_internalSideEdges_iff corridor hunique interior left.1).1 left.2).1
  have hrightBoundary :=
    ((mem_internalSideEdges_iff corridor hunique interior right.1).1 right.2).1
  let leftWitness := orbitFaceAcrossEdgeWitness RS htwoSided center left.1
    hleftBoundary
  let rightWitness := orbitFaceAcrossEdgeWitness RS htwoSided center right.1
    hrightBoundary
  have hacross : leftWitness.across = rightWitness.across := by
    simpa [leftWitness, rightWitness, center, corridor, internalSideNeighbor] using
      hfaces
  have hleftShared : left.1 ∈ sharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) center.1 leftWitness.across.1 :=
    (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
        ⟨leftWitness.edge_interior, hleftBoundary,
          leftWitness.edge_mem_across⟩
  have hrightShared : right.1 ∈ sharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) center.1 leftWitness.across.1 := by
    apply (mem_sharedInteriorEdges_iff (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).2
    refine ⟨rightWitness.edge_interior, hrightBoundary, ?_⟩
    rw [hacross]
    exact rightWitness.edge_mem_across
  exact (Finset.card_le_one_iff.1
    (hunique center.1 center.2 leftWitness.across.1 leftWitness.across.2
      (fun heq => leftWitness.face_ne_across (Subtype.ext heq))))
        hleftShared hrightShared

/-- Structural L1 slab conclusion for graph-backed normal-form fullerenes.
Every requested length occurs once the explicit bulk threshold is met; each
internal slab has four distinct external hexagonal side faces, while the
canonical corridor rungs are distinct and have only the two non-adjacent
local types. -/
theorem orbitFaceFullerene_exists_widthFourCleanHexCorridorSlab
    {G : SimpleGraph V} [DecidableRel G.Adj] (data : Data G)
    (hsphere : SphericalCubicMapData data.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hfullerene : OrbitFaceFullerene data.toRotationSystem)
    (hconnected : G.Connected)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (hcyclicFive : CyclicallyFiveEdgeConnected G)
    (corridorLength : Nat) (hpositive : 0 < corridorLength)
    (hlarge : 7 ^ (85 * corridorLength - 1) <
      Fintype.card (OrbitFace data.toRotationSystem)) :
    ∃ clean : CleanOrbitHexCorridorSkeleton
        data.toRotationSystem corridorLength,
      ∃ hunique : PairwiseUniqueSharedInteriorEdges
          (orbitFaceBoundary data.toRotationSystem)
          (Finset.univ : Finset (OrbitFace data.toRotationSystem)),
        Function.Injective
            (clean.toOrbitHexCorridorSkeleton.rungEdge hunique) ∧
        (∀ interior : CorridorInterior corridorLength,
          (internalSideEdges clean.toOrbitHexCorridorSkeleton
              hunique interior).card = 4 ∧
          Function.Injective
            (internalSideNeighbor clean htwoSided hunique interior) ∧
          ∀ side : {edge // edge ∈ internalSideEdges
              clean.toOrbitHexCorridorSkeleton hunique interior},
            (orbitFaceBoundary data.toRotationSystem
              (internalSideNeighbor clean htwoSided hunique interior side).1).card = 6 ∧
            ∀ index : Fin corridorLength,
              internalSideNeighbor clean htwoSided hunique interior side ≠
                clean.toOrbitHexCorridorSkeleton.faceAt index) ∧
        ∀ offset : Fin (corridorLength - 2),
          (internalHexRungTypeWord clean.toOrbitHexCorridorSkeleton
            htwoSided hunique offset) ≠ HexRungType.adjacent := by
  obtain ⟨clean, hunique, hrungs, htypes⟩ :=
    orbitFaceFullerene_exists_cleanInducedHexCorridor_with_twoRungTypes
      data hsphere htwoSided hfullerene hconnected hrotation hcyclicFive
        corridorLength hpositive hlarge
  exact ⟨clean, hunique, hrungs, fun interior =>
    ⟨card_internalSideEdges_eq_four clean.toOrbitHexCorridorSkeleton
        htwoSided hunique interior,
      internalSideNeighbor_injective clean htwoSided hunique interior,
      fun side =>
        ⟨internalSideNeighbor_hexagonal clean htwoSided hunique interior side,
          internalSideNeighbor_ne_faceAt clean htwoSided hunique interior side⟩⟩,
    htypes⟩

end

end GoertzelV24HexCorridorSlab

end Mettapedia.GraphTheory.FourColor
