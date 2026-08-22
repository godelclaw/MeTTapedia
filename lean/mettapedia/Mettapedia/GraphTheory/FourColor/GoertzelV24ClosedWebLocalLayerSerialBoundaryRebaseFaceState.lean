import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseTrackedState
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceRegionalDartGraph

/-!
# Exact finite facial state on the actual Cell boundary rebase

A primal edge has two literal darts even when both darts belong to the same
orbit face.  The four-edge boundary-rebase switch therefore exposes at most
eight face occurrences without requiring the false global assertion that the
opened annulus is face-two-sided.

This file transports those occurrences to eight fixed slots.  The extracted
state records which slots are occupied, which occurrences lie in the
pre-rebase region, their occurrence-sensitive regional face connectivity,
and the capped number of distinct primal edges in each predecessor component.
Counting the image under `edgeOf`, rather than the dart component itself,
prevents a twice-incident edge from being counted twice.

The adequacy theorems recover all four observations on every actual
occurrence.  Constructing the successor face rows from this state and the
local rebase geometry remains the next obligation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFaceStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- Literal dart occurrences over the actual four-edge rebase switch. -/
abbrev SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :=
  { dart : web.annular.RS.D //
    web.annular.RS.edgeOf dart ∈
      sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique offset hnext }

/-- Two darts per switch edge give at most eight literal facial occurrences.
No two-sidedness of quotient faces is used. -/
theorem sourceLocalLayerBoundaryRebaseFaceOccurrenceAt_card_le_eight
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fintype.card (SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) ≤ 8 := by
  let switch := sourceLocalLayerBoundaryRebaseSwitchAt corridor hunique
    offset hnext
  let darts := (Finset.univ : Finset web.annular.RS.D).filter fun dart =>
    web.annular.RS.edgeOf dart ∈ switch
  rw [Fintype.card_subtype]
  change darts.card ≤ 8
  have hmaps : (darts : Set web.annular.RS.D).MapsTo
      web.annular.RS.edgeOf switch := by
    intro dart hdart
    simpa [darts] using hdart
  have hcard : darts.card =
      ∑ edge ∈ switch, (web.annular.RS.dartsOn edge).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro edge hedge
    congr 1
    ext dart
    simp only [darts, RotationSystem.dartsOn, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · exact And.right
    · intro hdart
      exact ⟨hdart.symm ▸ hedge, hdart⟩
  calc
    darts.card = ∑ edge ∈ switch,
        (web.annular.RS.dartsOn edge).card := hcard
    _ = 2 * switch.card := by
      simp [web.annular.RS.dartsOn_card_two, mul_comm]
    _ ≤ 2 * 4 := Nat.mul_le_mul_left 2
      (card_sourceLocalLayerBoundaryRebaseSwitchAt_le_four
        corridor hunique offset hnext)
    _ = 8 := by omega

/-- A fixed finite occurrence state for the facial half of one rebase. -/
structure SourceLocalLayerBoundaryRebaseFaceState where
  slotOccupied : Fin 8 → Bool
  occurrencePresent : Fin 8 → Bool
  occurrenceConnected : Fin 8 → Fin 8 → Bool
  componentEdgeCap : Fin 8 → Fin 6

private def sourceLocalLayerBoundaryRebaseFaceStateEquiv :
    SourceLocalLayerBoundaryRebaseFaceState ≃
      (Fin 8 → Bool) × (Fin 8 → Bool) ×
        (Fin 8 → Fin 8 → Bool) × (Fin 8 → Fin 6) where
  toFun state :=
    ⟨state.slotOccupied, state.occurrencePresent,
      state.occurrenceConnected, state.componentEdgeCap⟩
  invFun state := ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : DecidableEq SourceLocalLayerBoundaryRebaseFaceState :=
  Classical.decEq _

noncomputable instance : Fintype SourceLocalLayerBoundaryRebaseFaceState := by
  letI : Fintype (Fin 8 → Bool) := Fintype.ofFinite _
  letI : Fintype (Fin 8 → Fin 8 → Bool) := Fintype.ofFinite _
  letI : Fintype (Fin 8 → Fin 6) := Fintype.ofFinite _
  exact Fintype.ofEquiv _ sourceLocalLayerBoundaryRebaseFaceStateEquiv.symm

/-- Canonical fixed slot of one actual switch occurrence. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor hunique offset
        hnext → Fin 8 :=
  fun occurrence => Fin.castLE
    (sourceLocalLayerBoundaryRebaseFaceOccurrenceAt_card_le_eight
      corridor hunique offset hnext)
    (Fintype.equivFin _ occurrence)

/-- Decode a fixed slot when it belongs to the canonical occupied prefix. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    Fin 8 → Option (SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) :=
  fun slot =>
    if hslot : slot.val < Fintype.card
        (SourceLocalLayerBoundaryRebaseFaceOccurrenceAt corridor hunique
          offset hnext) then
      some ((Fintype.equivFin _).symm ⟨slot.val, hslot⟩)
    else none

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?_slot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) :
    sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot? corridor hunique
        offset hnext
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext occurrence) = some occurrence := by
  simp [sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?,
    sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt]

/-- Distinct primal edges in the full predecessor face component of one
literal dart occurrence. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceComponentEdges
    (RS : RotationSystem V G.edgeSet) (region : Finset G.edgeSet)
    (start : RS.D) : Finset G.edgeSet := by
  classical
  exact ((Finset.univ : Finset RS.D).filter fun dart =>
    RS.edgeOf dart ∈ region ∧
      (faceRegionalDartGraph RS region).Reachable start dart).image RS.edgeOf

/-- Extract the exact fixed facial predecessor state from the actual
pre-rebase cumulative region. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFaceState := by
  classical
  let decode := sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?
    corridor hunique offset hnext
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  exact {
    slotOccupied := fun slot => decide (decode slot).isSome
    occurrencePresent := fun slot =>
      match decode slot with
      | some occurrence => decide (web.annular.RS.edgeOf occurrence.1 ∈ region)
      | none => false
    occurrenceConnected := fun left right =>
      match decode left, decode right with
      | some leftOccurrence, some rightOccurrence =>
          decide (graph.Reachable leftOccurrence.1 rightOccurrence.1)
      | _, _ => false
    componentEdgeCap := fun slot =>
      match decode slot with
      | some occurrence =>
          ⟨min (sourceLocalLayerBoundaryRebaseFaceComponentEdges
              web.annular.RS region occurrence.1).card 5,
            Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
      | none => ⟨0, by omega⟩ }

/-- Two occupied slots describe one predecessor regional face fragment when
both occurrences are present and connected in the literal face graph. -/
def SourceLocalLayerBoundaryRebaseFaceState.sameFragment
    (state : SourceLocalLayerBoundaryRebaseFaceState)
    (left right : Fin 8) : Prop :=
  state.slotOccupied left = true ∧ state.slotOccupied right = true ∧
    state.occurrencePresent left = true ∧
    state.occurrencePresent right = true ∧
    state.occurrenceConnected left right = true

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceStateAt_slotOccupied
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseFaceStateAt corridor hunique offset hnext
      ).slotOccupied
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext occurrence) = true := by
  simp [sourceLocalLayerBoundaryRebaseFaceStateAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceStateAt_occurrencePresent_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseFaceStateAt corridor hunique offset hnext
      ).occurrencePresent
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext occurrence) = true ↔
      web.annular.RS.edgeOf occurrence.1 ∈
        sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
          offset := by
  simp [sourceLocalLayerBoundaryRebaseFaceStateAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceStateAt_occurrenceConnected_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseFaceStateAt corridor hunique offset hnext
      ).occurrenceConnected
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext left)
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext right) = true ↔
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Reachable left.1 right.1 := by
  simp [sourceLocalLayerBoundaryRebaseFaceStateAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceStateAt_componentEdgeCap_val
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) :
    ((sourceLocalLayerBoundaryRebaseFaceStateAt corridor hunique offset hnext
      ).componentEdgeCap
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext occurrence)).val =
      min (sourceLocalLayerBoundaryRebaseFaceComponentEdges web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        occurrence.1).card 5 := by
  simp [sourceLocalLayerBoundaryRebaseFaceStateAt]

/-- On actual occurrence slots the finite same-fragment decoder is exactly
regional occurrence connectivity with both endpoint-presence guards. -/
theorem sourceLocalLayerBoundaryRebaseFaceStateAt_sameFragment_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) :
    (sourceLocalLayerBoundaryRebaseFaceStateAt corridor hunique offset hnext
      ).sameFragment
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext left)
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext right) ↔
      web.annular.RS.edgeOf left.1 ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        web.annular.RS.edgeOf right.1 ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          ).Reachable left.1 right.1 := by
  simp [SourceLocalLayerBoundaryRebaseFaceState.sameFragment]

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
