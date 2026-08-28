import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebPointwiseSelectedCellRebaseFiniteTransition
import Mettapedia.GraphTheory.FourColor.GoertzelV24RegionalProfileColorCongruence

/-!
# Local witnesses for a selected Cell--rebase transition

The source collar construction processes one literal Cell at a time.  Its old
proof-facing witness nevertheless supplied a positive colour on every edge of
the ambient opened graph.  This file removes that irrelevant suffix
coordinate.

For one Cell followed by its boundary rebase, the prefix colour is observed
only on the current terminal-aware region and on the four-role rebase switch.
We restrict witnesses to exactly that union, extend them by the fixed nonzero
colour `red` only as an adapter to the older constructor, and prove that the
exact source and target profiles are unchanged.  Consequently the image of
the realized transition relation is identical for local and ambient
witnesses.

The observed support is a realization interface, not the finite machine
state.  The machine state remains the bounded canonical profile/receipt
carrier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebPointwiseSelectedCellRebaseLocalWitness

open GoertzelV24AnnularInteriorFaceUniqueness
open GoertzelV24BoundaryProfileFiniteState
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Formation
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebPointwiseSelectedCellFiniteSupportLetter
open GoertzelV24ClosedWebPointwiseSelectedCellRebaseFiniteTransition
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexCorridorSkeleton

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance pointwiseSelectedCellRebaseLocalWitnessEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-! ## Exact observed support -/

/-- The only prefix edges read by one selected Cell--rebase step: the current
terminal-aware cumulative region, together with the at-most-four edges whose
regional status may change during boundary rebase. -/
noncomputable def pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) : Finset G.edgeSet :=
  pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
      corridor hinterior offset ∪
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
      hinterior offset hnext

theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_subset_observed
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior offset ⊆
      pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
        corridor hinterior offset hnext := by
  intro edge hedge
  exact Finset.mem_union_left _ hedge

theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_subset_observed
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation corridor
        hinterior offset hnext ⊆
      pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
        corridor hinterior offset hnext := by
  intro edge hedge
  exact Finset.mem_union_right _ hedge

/-- Beyond the cumulative terminal region, the observed prefix adds at most
the four rebase-role edges. -/
theorem card_observedPrefixRegion_sdiff_terminal_le_four
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :
    (pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
          corridor hinterior offset hnext \
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset).card ≤ 4 := by
  calc
    (pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
          corridor hinterior offset hnext \
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset).card ≤
        (pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext).card := by
      apply Finset.card_le_card
      intro edge hedge
      rcases Finset.mem_sdiff.mp hedge with ⟨hobserved, hnotTerminal⟩
      rcases Finset.mem_union.mp hobserved with hterminal | hswitch
      · exact (hnotTerminal hterminal).elim
      · exact hswitch
    _ ≤ 4 :=
      card_pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt_le_four
        formation corridor hinterior offset hnext

/-! ## Regional profile congruence -/

/-- The exact terminal-aware bounded profile reads no colour outside its
stored terminal region. -/
theorem pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt_eq_of_eq_on_region
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (left right : G.edgeSet → Color)
    (hleft : ∀ step,
      left (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step) ≠ 0)
    (hright : ∀ step,
      right (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
        hinterior offset step) ≠ 0)
    (heq : ∀ edge, edge ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior offset → left edge = right edge) :
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        formation corridor hinterior offset left hleft =
      pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt
        formation corridor hinterior offset right hright := by
  rw [GoertzelV24BoundaryProfileFiniteState.BoundedCorridorCutProfile.mk.injEq]
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  exact GraphCorridorCutData.regionalProfile_eq_of_eq_on_region
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt formation
      corridor hinterior offset)
    (pointwiseSelectedSourceLocalLayerSerialTerminalInputCutDataAt_portsInRegion
      formation corridor hinterior offset)
    left right hleft hright heq

/-- If two prefix colours agree on the observed support, adjoining the same
literal Cell gives identical colours throughout the successor terminal
region. -/
theorem pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_on_nextTerminal_of_eq_on_observed
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (leftPrefix rightPrefix cellColor : G.edgeSet → Color)
    (heq : ∀ edge, edge ∈
      pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
        corridor hinterior offset hnext →
      leftPrefix edge = rightPrefix edge) :
    ∀ edge, edge ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior (sourceLocalLayerNextOffset offset hnext) →
      pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation
          corridor hinterior offset leftPrefix cellColor edge =
        pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt formation
          corridor hinterior offset rightPrefix cellColor edge := by
  intro edge hnextRegion
  by_cases hcell : edge ∈
      pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
        hinterior offset
  · simp [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt, hcell]
  · simp only [pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt,
      if_neg hcell]
    apply heq edge
    by_cases hswitch : edge ∈
        pointwiseSelectedSourceLocalLayerBoundaryRebaseSwitchAt formation
          corridor hinterior offset hnext
    · exact Finset.mem_union_right _ hswitch
    · have hpre : edge ∈
          pointwiseSelectedSourceLocalLayerSerialPreRebaseOutputRegionAt
            formation corridor hinterior offset :=
        (pointwiseSelectedSourceLocalLayerSerialPreRebaseOutput_mem_iff_nextTerminalInput_of_not_mem_switch
          formation corridor hinterior offset hnext edge hswitch).2 hnextRegion
      rw [←
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt_union_cell
          formation corridor hinterior offset] at hpre
      rcases Finset.mem_union.mp hpre with hterminal | hcell'
      · exact Finset.mem_union_left _ hterminal
      · exact (hcell hcell').elim

/-- The selected successor profile reads only the successor terminal region. -/
theorem pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt_eq_of_eq_on_nextTerminal
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (left right : G.edgeSet → Color)
    (hleft : ∀ role,
      left (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0)
    (hright : ∀ role,
      right (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0)
    (heq : ∀ edge, edge ∈
      pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
        corridor hinterior (sourceLocalLayerNextOffset offset hnext) →
      left edge = right edge) :
    pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
        corridor hinterior offset hnext left hleft =
      pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
        corridor hinterior offset hnext right hright := by
  apply
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt_eq_of_eq_on_region
  exact heq

/-! ## Local and ambient realizations -/

/-- A positive prefix colour whose domain is exactly the support observed by
one selected Cell--rebase step. -/
abbrev PointwiseSelectedSourceLocalLayerSerialLocalPositivePrefixAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :=
  PointwiseSelectedPositiveColorFunction
    {edge : G.edgeSet // edge ∈
      pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
        corridor hinterior offset hnext}

/-- Extend a local prefix by `red` solely to call the older ambient witness
constructor.  No colour on the unprocessed suffix is carried by the local
witness. -/
noncomputable def extendPointwiseSelectedLocalPositivePrefixAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (localColor :
      PointwiseSelectedSourceLocalLayerSerialLocalPositivePrefixAt formation
        corridor hinterior offset hnext) :
    PointwiseSelectedPositiveColorFunction G.edgeSet :=
  ⟨fun edge => if hregion : edge ∈
        pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
          corridor hinterior offset hnext then
      localColor.1 ⟨edge, hregion⟩
    else red,
    by
      intro edge
      by_cases hregion : edge ∈
          pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt
            formation corridor hinterior offset hnext
      · simp [hregion, localColor.2]
      · simp [hregion]⟩

@[simp]
theorem extendPointwiseSelectedLocalPositivePrefixAt_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (localColor :
      PointwiseSelectedSourceLocalLayerSerialLocalPositivePrefixAt formation
        corridor hinterior offset hnext)
    (edge : G.edgeSet)
    (hregion : edge ∈
      pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
        corridor hinterior offset hnext) :
    (extendPointwiseSelectedLocalPositivePrefixAt formation corridor hinterior
      offset hnext localColor).1 edge = localColor.1 ⟨edge, hregion⟩ := by
  simp [extendPointwiseSelectedLocalPositivePrefixAt, hregion]

/-- Restrict an ambient prefix to the exact one-step observed support. -/
def restrictPointwiseSelectedPositivePrefixAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (ambientColor : PointwiseSelectedPositiveColorFunction G.edgeSet) :
    PointwiseSelectedSourceLocalLayerSerialLocalPositivePrefixAt formation
      corridor hinterior offset hnext :=
  ⟨fun edge => ambientColor.1 edge.1, fun edge => ambientColor.2 edge.1⟩

@[simp]
theorem extend_restrictPointwiseSelectedPositivePrefixAt_eq_of_mem
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (ambientColor : PointwiseSelectedPositiveColorFunction G.edgeSet)
    (edge : G.edgeSet)
    (hregion : edge ∈
      pointwiseSelectedSourceLocalLayerSerialObservedPrefixRegionAt formation
        corridor hinterior offset hnext) :
    (extendPointwiseSelectedLocalPositivePrefixAt formation corridor hinterior
      offset hnext
        (restrictPointwiseSelectedPositivePrefixAt formation corridor hinterior
          offset hnext ambientColor)).1 edge = ambientColor.1 edge := by
  simp [extendPointwiseSelectedLocalPositivePrefixAt,
    restrictPointwiseSelectedPositivePrefixAt, hregion]

/-- The former source witness: an ambient positive prefix, a literal Cell, and
agreement on their actual terminal overlap. -/
abbrev PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3)) :=
  { witness : PointwiseSelectedPositiveColorFunction G.edgeSet ×
      PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
        corridor hinterior offset //
    PointwiseSelectedSourceLocalLayerSerialTerminalCellColorsCompatibleAt
      formation corridor hinterior offset witness.1.1
        (pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
          hinterior offset witness.2) }

/-- The source-faithful witness: the prefix exists only on the one-step
observed support. -/
abbrev PointwiseSelectedSourceLocalLayerSerialLocalRealizationAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3) :=
  { witness :
      PointwiseSelectedSourceLocalLayerSerialLocalPositivePrefixAt formation
          corridor hinterior offset hnext ×
        PointwiseSelectedSourceLocalLayerCellLiteralOpenTaitColoringAt formation
          corridor hinterior offset //
    ∀ edge
      (hterminal : edge ∈
        pointwiseSelectedSourceLocalLayerSerialTerminalInputRegionAt formation
          corridor hinterior offset)
      (_hcell : edge ∈
        pointwiseSelectedSourceLocalLayerCellRegionAt formation corridor
          hinterior offset),
      witness.1.1
          ⟨edge, Finset.mem_union_left _ hterminal⟩ =
        pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
          hinterior offset witness.2 edge }

/-- Embed a local realization into the old ambient representation. -/
noncomputable def extendPointwiseSelectedLocalRealizationAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (witness : PointwiseSelectedSourceLocalLayerSerialLocalRealizationAt
      formation corridor hinterior offset hnext) :
    PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt formation
      corridor hinterior offset :=
  ⟨⟨extendPointwiseSelectedLocalPositivePrefixAt formation corridor
        hinterior offset hnext witness.1.1,
      witness.1.2⟩,
    by
      intro edge hterminal hcell
      rw [extendPointwiseSelectedLocalPositivePrefixAt_eq formation corridor
        hinterior offset hnext witness.1.1 edge
          (Finset.mem_union_left _ hterminal)]
      exact witness.2 edge hterminal hcell⟩

/-- Forget the unobserved suffix coordinate of an ambient realization. -/
def restrictPointwiseSelectedAmbientRealizationAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset) :
    PointwiseSelectedSourceLocalLayerSerialLocalRealizationAt formation
      corridor hinterior offset hnext :=
  ⟨⟨restrictPointwiseSelectedPositivePrefixAt formation corridor
        hinterior offset hnext witness.1.1,
      witness.1.2⟩,
    by
      intro edge hterminal hcell
      exact witness.2 edge hterminal hcell⟩

/-! ## Exact transition endpoints -/

/-- Exact source endpoint represented by an ambient realization. -/
noncomputable def pointwiseSelectedAmbientRealizationSourceAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset) :
    BoundedCorridorCutProfile 2 1 4 :=
  pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt formation
    corridor hinterior offset witness.1.1.1 (fun step =>
      witness.1.1.2
        (pointwiseSelectedSourceLocalLayerLeftCrossingAt formation corridor
          hinterior offset step))

/-- Exact target endpoint represented by an ambient realization. -/
noncomputable def pointwiseSelectedAmbientRealizationTargetAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset) :
    BoundedCorridorCutProfile 2 1 4 := by
  let cellColor :=
    pointwiseSelectedSourceLocalLayerCellLiteralColorAt formation corridor
      hinterior offset witness.1.2
  let spliced := pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt
    formation corridor hinterior offset witness.1.1.1 cellColor
  let hrole : ∀ role,
      spliced (pointwiseSelectedSourceLocalLayerBoundaryRebaseEdgeAt formation
        corridor hinterior offset hnext role) ≠ 0 :=
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_boundaryRebaseEdge_ne_zero
      formation corridor hinterior offset hnext witness.1.1.1 witness.1.1.2
        witness.1.2
  exact pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt formation
    corridor hinterior offset hnext spliced hrole

/-- The exact local endpoints are defined through the representation adapter;
the theorem below proves that the adapter does not change the image. -/
noncomputable def pointwiseSelectedLocalRealizationEndpointsAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (witness : PointwiseSelectedSourceLocalLayerSerialLocalRealizationAt
      formation corridor hinterior offset hnext) :
    BoundedCorridorCutProfile 2 1 4 × BoundedCorridorCutProfile 2 1 4 :=
  let ambient := extendPointwiseSelectedLocalRealizationAt formation corridor
    hinterior offset hnext witness
  ⟨pointwiseSelectedAmbientRealizationSourceAt formation corridor hinterior
      offset ambient,
    pointwiseSelectedAmbientRealizationTargetAt formation corridor hinterior
      offset hnext ambient⟩

/-- Restricting and re-extending an ambient witness preserves the exact source
profile. -/
theorem pointwiseSelectedAmbientRealizationSourceAt_extend_restrict_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset) :
    pointwiseSelectedAmbientRealizationSourceAt formation corridor hinterior
        offset
        (extendPointwiseSelectedLocalRealizationAt formation corridor hinterior
          offset hnext
            (restrictPointwiseSelectedAmbientRealizationAt formation corridor
              hinterior offset hnext witness)) =
      pointwiseSelectedAmbientRealizationSourceAt formation corridor hinterior
        offset witness := by
  unfold pointwiseSelectedAmbientRealizationSourceAt
  apply
    pointwiseSelectedSourceLocalLayerSerialTerminalInputBoundedProfileAt_eq_of_eq_on_region
  intro edge hterminal
  exact extend_restrictPointwiseSelectedPositivePrefixAt_eq_of_mem formation
    corridor hinterior offset hnext witness.1.1 edge
      (Finset.mem_union_left _ hterminal)

/-- Restricting and re-extending an ambient witness preserves the exact target
profile.  This is the two-sided locality statement: current-prefix colours
plus the finite rebase switch determine every colour read after the move. -/
theorem pointwiseSelectedAmbientRealizationTargetAt_extend_restrict_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset) :
    pointwiseSelectedAmbientRealizationTargetAt formation corridor hinterior
        offset hnext
        (extendPointwiseSelectedLocalRealizationAt formation corridor hinterior
          offset hnext
            (restrictPointwiseSelectedAmbientRealizationAt formation corridor
              hinterior offset hnext witness)) =
      pointwiseSelectedAmbientRealizationTargetAt formation corridor hinterior
        offset hnext witness := by
  unfold pointwiseSelectedAmbientRealizationTargetAt
  apply
    pointwiseSelectedSourceLocalLayerBoundaryRebaseOutputForColorAt_eq_of_eq_on_nextTerminal
  apply
    pointwiseSelectedSourceLocalLayerSerialCellSplicedColorAt_eq_on_nextTerminal_of_eq_on_observed
  intro edge hobserved
  exact extend_restrictPointwiseSelectedPositivePrefixAt_eq_of_mem formation
    corridor hinterior offset hnext witness.1.1 edge hobserved

/-- The local endpoint pair obtained after restricting an ambient realization
is literally the original ambient endpoint pair. -/
theorem pointwiseSelectedLocalRealizationEndpointsAt_restrict_eq
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset) :
    pointwiseSelectedLocalRealizationEndpointsAt formation corridor hinterior
        offset hnext
        (restrictPointwiseSelectedAmbientRealizationAt formation corridor
          hinterior offset hnext witness) =
      ⟨pointwiseSelectedAmbientRealizationSourceAt formation corridor hinterior
          offset witness,
        pointwiseSelectedAmbientRealizationTargetAt formation corridor hinterior
          offset hnext witness⟩ := by
  apply Prod.ext
  · exact pointwiseSelectedAmbientRealizationSourceAt_extend_restrict_eq
      formation corridor hinterior offset hnext witness
  · exact pointwiseSelectedAmbientRealizationTargetAt_extend_restrict_eq
      formation corridor hinterior offset hnext witness

/-! ## Equality of realized transition images -/

/-- Realized transition image for the former ambient witness representation. -/
def PointwiseSelectedAmbientRealizedTransitionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (source target : BoundedCorridorCutProfile 2 1 4) : Prop :=
  ∃ witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset,
    pointwiseSelectedAmbientRealizationSourceAt formation corridor hinterior
        offset witness = source ∧
      pointwiseSelectedAmbientRealizationTargetAt formation corridor hinterior
        offset hnext witness = target

/-- Realized transition image with no ambient suffix-colour coordinate. -/
def PointwiseSelectedLocalRealizedTransitionAt
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (source target : BoundedCorridorCutProfile 2 1 4) : Prop :=
  ∃ witness : PointwiseSelectedSourceLocalLayerSerialLocalRealizationAt
      formation corridor hinterior offset hnext,
    pointwiseSelectedLocalRealizationEndpointsAt formation corridor hinterior
      offset hnext witness = ⟨source, target⟩

/-- Exact representation invariance of the selected Cell--rebase transition:
local observed-support witnesses and ambient whole-graph prefix witnesses have
identical source/target images. -/
theorem pointwiseSelectedLocalRealizedTransitionAt_iff_ambient
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (source target : BoundedCorridorCutProfile 2 1 4) :
    PointwiseSelectedLocalRealizedTransitionAt formation corridor hinterior
        offset hnext source target ↔
      PointwiseSelectedAmbientRealizedTransitionAt formation corridor hinterior
        offset hnext source target := by
  constructor
  · rintro ⟨witness, hendpoints⟩
    let ambient := extendPointwiseSelectedLocalRealizationAt formation corridor
      hinterior offset hnext witness
    refine ⟨ambient, ?_, ?_⟩
    · exact congrArg Prod.fst hendpoints
    · exact congrArg Prod.snd hendpoints
  · rintro ⟨witness, hsource, htarget⟩
    refine ⟨restrictPointwiseSelectedAmbientRealizationAt formation corridor
      hinterior offset hnext witness, ?_⟩
    rw [pointwiseSelectedLocalRealizationEndpointsAt_restrict_eq formation
      corridor hinterior offset hnext witness, hsource, htarget]

/-! ## Soundness into the canonical finite machine -/

/-- The canonical finite letter extracted from an ambient realization runs
between exactly the two endpoints named above. -/
theorem pointwiseSelectedAmbientRealization_finiteLetter_transition
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (witness : PointwiseSelectedSourceLocalLayerSerialAmbientRealizationAt
      formation corridor hinterior offset) :
    let letter :=
      pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt formation
        corridor hinterior offset hnext hcell witness.1.1 witness.1.2
    letter.Transition
      (pointwiseSelectedAmbientRealizationSourceAt formation corridor hinterior
        offset witness)
      (pointwiseSelectedAmbientRealizationTargetAt formation corridor hinterior
        offset hnext witness) := by
  simpa [pointwiseSelectedAmbientRealizationSourceAt,
    pointwiseSelectedAmbientRealizationTargetAt,
    pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt,
    pointwiseSelectedSourceLocalLayerSerialCellFiniteSupportLetterAt,
    pointwiseSelectedSourceLocalLayerBoundaryRebaseNormalizedSupportLetterForColorAt]
    using
    (pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt_transition
      formation corridor hinterior offset hnext hcell witness.1.1 witness.1.2
        witness.2)

/-- Every locally realized transition is a transition of the canonical finite
Cell--rebase machine.  The converse is deliberately not claimed here: proving
that every abstract supported letter is physically realizable is the separate
closure-completeness obligation. -/
theorem pointwiseSelectedLocalRealizedTransitionAt_finiteTransition
    {data : AnnularBoundaryData G 5} (formation : Formation data)
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor formation.annular blockLength)
    (hinterior : InteriorPairwiseUniqueSharedInteriorEdges
      formation.annular.cellulation)
    (offset : Fin (blockLength - 3))
    (hnext : offset.val + 1 < blockLength - 3)
    (hcell : (pointwiseSelectedSourceLocalLayerCellRegionAt formation
      corridor hinterior offset).card ≤ 6)
    (source target : BoundedCorridorCutProfile 2 1 4)
    (hrealized : PointwiseSelectedLocalRealizedTransitionAt formation corridor
      hinterior offset hnext source target) :
    PointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteTransition source
      target := by
  have hambient :=
    (pointwiseSelectedLocalRealizedTransitionAt_iff_ambient formation corridor
      hinterior offset hnext source target).1 hrealized
  rcases hambient with ⟨witness, hsource, htarget⟩
  refine ⟨pointwiseSelectedSourceLocalLayerSerialCellRebaseFiniteLetterAt
    formation corridor hinterior offset hnext hcell witness.1.1 witness.1.2,
    ?_⟩
  have htransition :=
    pointwiseSelectedAmbientRealization_finiteLetter_transition formation
      corridor hinterior offset hnext hcell witness
  simpa [hsource, htarget] using htransition

end

end GoertzelV24ClosedWebPointwiseSelectedCellRebaseLocalWitness

end Mettapedia.GraphTheory.FourColor
