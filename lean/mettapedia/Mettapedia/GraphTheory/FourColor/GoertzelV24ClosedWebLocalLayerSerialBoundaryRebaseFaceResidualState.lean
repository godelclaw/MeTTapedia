import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialBoundaryRebaseFaceState

/-!
# Residual facial factorization on the actual Cell boundary rebase

The occurrence state records full predecessor connectivity on the finite
switch, but deleting a switch edge can split such a component.  A sound
successor update must therefore distinguish paths through the persistent old
boundary fragments from components which meet no old boundary fragment.

This file adds exactly that finite factorization.  The old two-edge cut has at
most four occurrence-sensitive boundary fragments.  They are transported to
four fixed slots, and each of the eight switch-occurrence slots records its
attachments and its port-free residual component.  The final theorem proves
that this data reconstructs predecessor reachability between every pair of
actual present occurrences.

No successor facial row or reachable-set estimate is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAtGoodWord

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance closedWebLocalLayerSerialBoundaryRebaseFaceResidualStateEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace Instance

namespace LocalLayerFormation

/-- The actual occurrence-sensitive boundary fragments of the pre-rebase
two-edge output cut. -/
abbrev SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :=
  BoundaryRegionalFragment web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerRightCrossingAt corridor hunique offset))
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)

/-- A two-edge cut exposes at most four literal old boundary fragments. -/
theorem sourceLocalLayerBoundaryRebaseOldFaceFragmentAt_card_le_four
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Fintype.card (SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
      corridor hunique offset) ≤ 4 := by
  simpa using
    (regionalBoundaryGraphCutData_fragmentCount_le_two_mul
      web.annular.RS
      (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
      (sourceLocalLayerRightCrossingAt corridor hunique offset))

/-- Fixed residual data relative to the four old-fragment slots. -/
structure SourceLocalLayerBoundaryRebaseFaceResidualState where
  occurrenceState : SourceLocalLayerBoundaryRebaseFaceState
  oldFragmentOccupied : Fin 4 → Bool
  occurrenceAttaches : Fin 8 → Fin 4 → Bool
  residualConnected : Fin 8 → Fin 8 → Bool

private def sourceLocalLayerBoundaryRebaseFaceResidualStateEquiv :
    SourceLocalLayerBoundaryRebaseFaceResidualState ≃
      SourceLocalLayerBoundaryRebaseFaceState ×
        (Fin 4 → Bool) × (Fin 8 → Fin 4 → Bool) ×
          (Fin 8 → Fin 8 → Bool) where
  toFun state :=
    ⟨state.occurrenceState, state.oldFragmentOccupied,
      state.occurrenceAttaches, state.residualConnected⟩
  invFun state := ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance :
    DecidableEq SourceLocalLayerBoundaryRebaseFaceResidualState :=
  Classical.decEq _

noncomputable instance :
    Fintype SourceLocalLayerBoundaryRebaseFaceResidualState := by
  letI : Fintype (Fin 4 → Bool) := Fintype.ofFinite _
  letI : Fintype (Fin 8 → Fin 4 → Bool) := Fintype.ofFinite _
  letI : Fintype (Fin 8 → Fin 8 → Bool) := Fintype.ofFinite _
  exact Fintype.ofEquiv _
    sourceLocalLayerBoundaryRebaseFaceResidualStateEquiv.symm

/-- Canonical fixed slot of one actual predecessor boundary fragment. -/
noncomputable def sourceLocalLayerBoundaryRebaseOldFaceFragmentSlotAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    SourceLocalLayerBoundaryRebaseOldFaceFragmentAt corridor hunique offset →
      Fin 4 :=
  fun fragment => Fin.castLE
    (sourceLocalLayerBoundaryRebaseOldFaceFragmentAt_card_le_four
      corridor hunique offset)
    (Fintype.equivFin _ fragment)

/-- Decode an occupied old-fragment slot. -/
noncomputable def sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot?
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3)) :
    Fin 4 → Option (SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
      corridor hunique offset) :=
  fun slot =>
    if hslot : slot.val < Fintype.card
        (SourceLocalLayerBoundaryRebaseOldFaceFragmentAt corridor hunique
          offset) then
      some ((Fintype.equivFin _).symm ⟨slot.val, hslot⟩)
    else none

@[simp]
theorem sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot?_slot
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
      corridor hunique offset) :
    sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot? corridor hunique
        offset
        (sourceLocalLayerBoundaryRebaseOldFaceFragmentSlotAt corridor hunique
          offset fragment) = some fragment := by
  simp [sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot?,
    sourceLocalLayerBoundaryRebaseOldFaceFragmentSlotAt]

/-- The canonical literal dart occurrence of an old boundary fragment. -/
noncomputable def sourceLocalLayerBoundaryRebaseOldFaceFragmentDartAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (fragment : SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
      corridor hunique offset) : web.annular.RS.D :=
  (boundaryRegionalFragmentDartOccurrence web.annular.RS
    (indexedCrossingEdgeSet
      (sourceLocalLayerRightCrossingAt corridor hunique offset))
    (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    fragment).1

/-- Exact fixed residual facial state of the actual pre-rebase region. -/
noncomputable def sourceLocalLayerBoundaryRebaseFaceResidualStateAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    SourceLocalLayerBoundaryRebaseFaceResidualState := by
  classical
  let occurrenceDecode := sourceLocalLayerBoundaryRebaseFaceOccurrenceAtSlot?
    corridor hunique offset hnext
  let fragmentDecode := sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot?
    corridor hunique offset
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  let fragmentDart := sourceLocalLayerBoundaryRebaseOldFaceFragmentDartAt
    corridor hunique offset
  exact {
    occurrenceState :=
      sourceLocalLayerBoundaryRebaseFaceStateAt corridor hunique offset hnext
    oldFragmentOccupied := fun slot => (fragmentDecode slot).isSome
    occurrenceAttaches := fun occurrenceSlot fragmentSlot =>
      match occurrenceDecode occurrenceSlot, fragmentDecode fragmentSlot with
      | some occurrence, some fragment =>
          decide (web.annular.RS.edgeOf occurrence.1 ∈ region ∧
            graph.Reachable occurrence.1 (fragmentDart fragment))
      | _, _ => false
    residualConnected := fun leftSlot rightSlot =>
      match occurrenceDecode leftSlot, occurrenceDecode rightSlot with
      | some left, some right =>
          decide (web.annular.RS.edgeOf left.1 ∈ region ∧
            web.annular.RS.edgeOf right.1 ∈ region ∧
            graph.Reachable left.1 right.1 ∧
            ∀ fragment, ¬ graph.Reachable left.1 (fragmentDart fragment))
      | _, _ => false }

/-- Graph-free interpretation of the finite old-fragment factorization. -/
def SourceLocalLayerBoundaryRebaseFaceResidualState.factoredReachable
    (state : SourceLocalLayerBoundaryRebaseFaceResidualState)
    (left right : Fin 8) : Prop :=
  state.residualConnected left right = true ∨
    ∃ fragment : Fin 4,
      state.oldFragmentOccupied fragment = true ∧
        state.occurrenceAttaches left fragment = true ∧
        state.occurrenceAttaches right fragment = true

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceResidualStateAt_oldFragmentOccupied
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (fragment : SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
      corridor hunique offset) :
    (sourceLocalLayerBoundaryRebaseFaceResidualStateAt corridor hunique offset
      hnext).oldFragmentOccupied
        (sourceLocalLayerBoundaryRebaseOldFaceFragmentSlotAt corridor hunique
          offset fragment) = true := by
  simp [sourceLocalLayerBoundaryRebaseFaceResidualStateAt]

theorem sourceLocalLayerBoundaryRebaseFaceResidualStateAt_oldFragmentOccupied_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) (slot : Fin 4) :
    (sourceLocalLayerBoundaryRebaseFaceResidualStateAt corridor hunique offset
      hnext).oldFragmentOccupied slot = true ↔
      ∃ fragment, sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot?
        corridor hunique offset slot = some fragment := by
  classical
  simp only [sourceLocalLayerBoundaryRebaseFaceResidualStateAt]
  cases sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot?
      corridor hunique offset slot <;> simp

theorem sourceLocalLayerBoundaryRebaseFaceResidualStateAt_attaches_iff_of_decode
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext) (slot : Fin 4)
    (fragment : SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
      corridor hunique offset)
    (hdecode : sourceLocalLayerBoundaryRebaseOldFaceFragmentAtSlot?
      corridor hunique offset slot = some fragment) :
    (sourceLocalLayerBoundaryRebaseFaceResidualStateAt corridor hunique offset
      hnext).occurrenceAttaches
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext occurrence) slot = true ↔
      web.annular.RS.edgeOf occurrence.1 ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          ).Reachable occurrence.1
            (sourceLocalLayerBoundaryRebaseOldFaceFragmentDartAt corridor
              hunique offset fragment) := by
  classical
  simp [sourceLocalLayerBoundaryRebaseFaceResidualStateAt, hdecode]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceResidualStateAt_attaches_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (occurrence : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext)
    (fragment : SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
      corridor hunique offset) :
    (sourceLocalLayerBoundaryRebaseFaceResidualStateAt corridor hunique offset
      hnext).occurrenceAttaches
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext occurrence)
        (sourceLocalLayerBoundaryRebaseOldFaceFragmentSlotAt corridor hunique
          offset fragment) = true ↔
      web.annular.RS.edgeOf occurrence.1 ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          ).Reachable occurrence.1
            (sourceLocalLayerBoundaryRebaseOldFaceFragmentDartAt corridor
              hunique offset fragment) := by
  simp [sourceLocalLayerBoundaryRebaseFaceResidualStateAt]

@[simp]
theorem sourceLocalLayerBoundaryRebaseFaceResidualStateAt_residual_iff
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
    (sourceLocalLayerBoundaryRebaseFaceResidualStateAt corridor hunique offset
      hnext).residualConnected
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext left)
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext right) = true ↔
      web.annular.RS.edgeOf left.1 ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        web.annular.RS.edgeOf right.1 ∈
          sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset ∧
        (faceRegionalDartGraph web.annular.RS
          (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
          ).Reachable left.1 right.1 ∧
        ∀ fragment : SourceLocalLayerBoundaryRebaseOldFaceFragmentAt
            corridor hunique offset,
          ¬ (faceRegionalDartGraph web.annular.RS
            (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
            ).Reachable left.1
              (sourceLocalLayerBoundaryRebaseOldFaceFragmentDartAt corridor
                hunique offset fragment) := by
  simp [sourceLocalLayerBoundaryRebaseFaceResidualStateAt]

/-- On present actual occurrences, the fixed finite residual state recovers
the complete predecessor regional-face reachability relation. -/
theorem sourceLocalLayerBoundaryRebaseFaceResidualStateAt_factoredReachable_iff
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : Instance data coloring} {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : SourceLocalLayerBoundaryRebaseFaceOccurrenceAt
      corridor hunique offset hnext)
    (hleft : web.annular.RS.edgeOf left.1 ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
    (hright : web.annular.RS.edgeOf right.1 ∈
      sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset) :
    (sourceLocalLayerBoundaryRebaseFaceResidualStateAt corridor hunique offset
      hnext).factoredReachable
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext left)
        (sourceLocalLayerBoundaryRebaseFaceOccurrenceSlotAt corridor hunique
          offset hnext right) ↔
      (faceRegionalDartGraph web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        ).Reachable left.1 right.1 := by
  let region := sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique
    offset
  let graph := faceRegionalDartGraph web.annular.RS region
  constructor
  · intro hfactored
    rcases hfactored with hresidual |
      ⟨fragmentSlot, hoccupied, hleftAttach, hrightAttach⟩
    · exact
        ((sourceLocalLayerBoundaryRebaseFaceResidualStateAt_residual_iff
          corridor hunique offset hnext left right).1 hresidual).2.2.1
    · rcases
        (sourceLocalLayerBoundaryRebaseFaceResidualStateAt_oldFragmentOccupied_iff
          corridor hunique offset hnext fragmentSlot).1 hoccupied with
          ⟨fragment, hdecode⟩
      have hleftData :=
        (sourceLocalLayerBoundaryRebaseFaceResidualStateAt_attaches_iff_of_decode
          corridor hunique offset hnext left fragmentSlot fragment hdecode).1
            hleftAttach
      have hrightData :=
        (sourceLocalLayerBoundaryRebaseFaceResidualStateAt_attaches_iff_of_decode
          corridor hunique offset hnext right fragmentSlot fragment hdecode).1
            hrightAttach
      exact hleftData.2.trans hrightData.2.symm
  · intro hreachable
    by_cases hfragment : ∃ fragment :
        SourceLocalLayerBoundaryRebaseOldFaceFragmentAt corridor hunique offset,
      graph.Reachable left.1
        (sourceLocalLayerBoundaryRebaseOldFaceFragmentDartAt corridor hunique
          offset fragment)
    · rcases hfragment with ⟨fragment, hleftFragment⟩
      apply Or.inr
      refine ⟨sourceLocalLayerBoundaryRebaseOldFaceFragmentSlotAt corridor
        hunique offset fragment, ?_, ?_, ?_⟩
      · exact sourceLocalLayerBoundaryRebaseFaceResidualStateAt_oldFragmentOccupied
          corridor hunique offset hnext fragment
      · apply
          (sourceLocalLayerBoundaryRebaseFaceResidualStateAt_attaches_iff
            corridor hunique offset hnext left fragment).2
        exact ⟨hleft, hleftFragment⟩
      · apply
          (sourceLocalLayerBoundaryRebaseFaceResidualStateAt_attaches_iff
            corridor hunique offset hnext right fragment).2
        exact ⟨hright, hreachable.symm.trans hleftFragment⟩
    · apply Or.inl
      apply
        (sourceLocalLayerBoundaryRebaseFaceResidualStateAt_residual_iff
          corridor hunique offset hnext left right).2
      exact ⟨hleft, hright, hreachable, by
        intro fragment hreach
        exact hfragment ⟨fragment, hreach⟩⟩

end LocalLayerFormation

end Instance

end

end GoertzelV24ClosedWebAtGoodWord

end Mettapedia.GraphTheory.FourColor
