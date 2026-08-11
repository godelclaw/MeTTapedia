import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorPrefixProfileFaceUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceSliceFragments

/-!
# Finite face coordinates for one source Cell update

The occurrence-level update identifies the enlarged prefix fragments as the
closure of old-prefix fragments, Cell fragments, and the two literal corner
turns.  This file transports the corresponding cap-at-five arithmetic to the
actual boundary-fragment carrier of the outgoing source cross-section.

For each outgoing fragment, its contribution from either factor is the
disjoint union of every factor fragment meeting it.  The two factor slices
overlap only on the single shared rung, which is subtracted exactly once.
No deterministic successor profile is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24GraphDerivedCorridorCutProfile
open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RegionalBoundaryProfileFiniteState
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationFaceFragments
open GoertzelV24TerminalProfileFaceCapUpdate
open GoertzelV24TerminalProfileFaceSliceFragments
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorPrefixProfileFaceCoordinatesEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Transporting a boundary fragment along an equality of regional edge sets
does not change its literal edge support. -/
theorem boundaryRegionalFragmentEdges_equivCast
    (RS : RotationSystem V G.edgeSet) (cut : Finset G.edgeSet)
    {leftRegion rightRegion : Finset G.edgeSet}
    (hregion : leftRegion = rightRegion)
    (fragment : BoundaryRegionalFragment RS cut leftRegion) :
    boundaryRegionalFragmentEdges RS cut rightRegion
        (Equiv.cast
          (congrArg (fun region => BoundaryRegionalFragment RS cut region)
            hregion)
          fragment) =
      boundaryRegionalFragmentEdges RS cut leftRegion fragment := by
  subst rightRegion
  rfl

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

/-- The boundary-fragment carrier on the literal union of the old prefix and
one source Cell.  This union is propositionally equal to the outgoing prefix
region. -/
abbrev LocalLayerComposedBoundaryFragment
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :=
  BoundaryRegionalFragment
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
    (interface.localLayerLeftPrefixRegion ∪
      interface.localLayerCellBoundaryRegion)

/-- Reindex the graph-derived outgoing carrier along the proved literal
region equality.  No fragment is chosen or discarded. -/
noncomputable def localLayerRightPrefixBoundaryFragmentEquiv
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext) :
    BoundaryRegionalFragment
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion ≃
      interface.LocalLayerComposedBoundaryFragment :=
  Equiv.cast <| congrArg
    (fun region => BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing) region)
    interface.localLayerRightPrefixRegion_eq_left_union_cell

/-- Reindexing the outgoing carrier preserves the fragment's literal edge
support. -/
theorem localLayerRightPrefixBoundaryFragmentEquiv_edges
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion) :
    boundaryRegionalFragmentEdges
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        (interface.localLayerLeftPrefixRegion ∪
          interface.localLayerCellBoundaryRegion)
        (interface.localLayerRightPrefixBoundaryFragmentEquiv fragment) =
      boundaryRegionalFragmentEdges
        embedded.cellulation.rotation.toRotationSystem
        (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
        interface.localLayerRightPrefixRegion fragment := by
  exact boundaryRegionalFragmentEdges_equivCast
    embedded.cellulation.rotation.toRotationSystem
    (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
    interface.localLayerRightPrefixRegion_eq_left_union_cell fragment

/-- The outgoing graph-cut coordinate, transported to the literal
prefix-plus-Cell carrier. -/
noncomputable def localLayerRightPrefixBoundaryFragmentAt
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (index : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion))) :
    interface.LocalLayerComposedBoundaryFragment :=
  interface.localLayerRightPrefixBoundaryFragmentEquiv
    (boundaryRegionalFragmentAt
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion index)

/-- The capped contribution of all fragments of one factor region meeting a
fixed outgoing fragment. -/
def localLayerFactorFragmentCapSum
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (factorRegion : Finset G.edgeSet)
    (fragment : interface.LocalLayerComposedBoundaryFragment) : Nat :=
  min
    (∑ factorFragment ∈ faceRegionalFactorFragments
          embedded.cellulation.rotation.toRotationSystem
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            fragment.1.1)
          (interface.localLayerLeftPrefixRegion ∪
            interface.localLayerCellBoundaryRegion)
          factorRegion fragment.2.1,
        min (faceRegionalFragmentPositions
          embedded.cellulation.rotation.toRotationSystem
          (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
            fragment.1.1)
          factorRegion factorFragment).card 5)
    5

/-- The genuine occurrence overlap of the old-prefix and Cell slices inside
one outgoing fragment. -/
def localLayerFactorFragmentOverlapCard
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : interface.LocalLayerComposedBoundaryFragment) : Nat :=
  (faceRegionalFragmentPositionSlice
        embedded.cellulation.rotation.toRotationSystem
        (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
          fragment.1.1)
        (interface.localLayerLeftPrefixRegion ∪
          interface.localLayerCellBoundaryRegion)
        interface.localLayerLeftPrefixRegion fragment.2.1 ∩
    faceRegionalFragmentPositionSlice
        embedded.cellulation.rotation.toRotationSystem
        (orbitFaceRoot embedded.cellulation.rotation.toRotationSystem
          fragment.1.1)
        (interface.localLayerLeftPrefixRegion ∪
          interface.localLayerCellBoundaryRegion)
        interface.localLayerCellBoundaryRegion fragment.2.1).card

/-- Exact cap-at-five update for one outgoing boundary fragment.  All old
prefix and Cell fragments that meet it contribute, and their common
occurrences on the single shared rung are removed once. -/
theorem localLayerRightPrefixBoundaryFragment_cap_eq_factorCaps
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (fragment : interface.LocalLayerComposedBoundaryFragment) :
    min (boundaryRegionalFragmentEdges
          embedded.cellulation.rotation.toRotationSystem
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          (interface.localLayerLeftPrefixRegion ∪
            interface.localLayerCellBoundaryRegion) fragment).card 5 =
      min
        (interface.localLayerFactorFragmentCapSum
            interface.localLayerLeftPrefixRegion fragment +
          interface.localLayerFactorFragmentCapSum
            interface.localLayerCellBoundaryRegion fragment -
          interface.localLayerFactorFragmentOverlapCard fragment)
        5 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let root := orbitFaceRoot RS fragment.1.1
  change min (faceRegionalFragmentEdges RS root
      (interface.localLayerLeftPrefixRegion ∪
        interface.localLayerCellBoundaryRegion) fragment.2.1).card 5 = _
  have hseam :
      (interface.localLayerLeftPrefixRegion ∩
          interface.localLayerCellBoundaryRegion).card < 5 := by
    rw [interface.localLayerLeftPrefixRegion_inter_cellBoundary_eq_singleton]
    simp
  have hcap :=
    min_card_faceRegionalFragmentEdges_union_eq_min_slices_sub_inter
      RS htwoSided root interface.localLayerLeftPrefixRegion
        interface.localLayerCellBoundaryRegion fragment.2.1 hseam
  rw [min_card_faceRegionalFragmentPositionSlice_eq_min_sum_fragmentCaps
      RS root
      (interface.localLayerLeftPrefixRegion ∪
        interface.localLayerCellBoundaryRegion)
      interface.localLayerLeftPrefixRegion Finset.subset_union_left
      fragment.2.1,
    min_card_faceRegionalFragmentPositionSlice_eq_min_sum_fragmentCaps
      RS root
      (interface.localLayerLeftPrefixRegion ∪
        interface.localLayerCellBoundaryRegion)
      interface.localLayerCellBoundaryRegion Finset.subset_union_right
      fragment.2.1] at hcap
  simpa [RS, root, localLayerFactorFragmentCapSum,
    localLayerFactorFragmentOverlapCard] using hcap

/-- The cap field stored at every actual outgoing finite-profile coordinate
is the overlap-corrected capped sum of the old-prefix and Cell factor
fragments that meet it. -/
theorem localLayerRightPrefixBoundedProfile_faceLengthCap_eq_factorCaps
    (interface : SourceConsecutiveSlabInterface realization htwoSided hunique
      leftInterior hnext)
    (color : G.edgeSet → Color)
    (hcolor : ∀ step, color (interface.nextLocalLayerPrefixCrossing step) ≠ 0)
    (index : Fin (Fintype.card (BoundaryRegionalFragment
      embedded.cellulation.rotation.toRotationSystem
      (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
      interface.localLayerRightPrefixRegion))) :
    (((interface.localLayerRightPrefixBoundedProfile color hcolor).profile
        |>.faceLengthCap index).val) =
      min
        (interface.localLayerFactorFragmentCapSum
            interface.localLayerLeftPrefixRegion
            (interface.localLayerRightPrefixBoundaryFragmentAt index) +
          interface.localLayerFactorFragmentCapSum
            interface.localLayerCellBoundaryRegion
            (interface.localLayerRightPrefixBoundaryFragmentAt index) -
          interface.localLayerFactorFragmentOverlapCard
            (interface.localLayerRightPrefixBoundaryFragmentAt index))
        5 := by
  let RS := embedded.cellulation.rotation.toRotationSystem
  let actualFragment := boundaryRegionalFragmentAt RS
    (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
    interface.localLayerRightPrefixRegion index
  have hfragmentEdges :
      (interface.localLayerRightPrefixGraphCutData.regionalFragmentEdges index) =
        boundaryRegionalFragmentEdges RS
          (indexedCrossingEdgeSet interface.nextLocalLayerPrefixCrossing)
          interface.localLayerRightPrefixRegion actualFragment := by
    rw [interface.localLayerRightPrefixGraphCutData
      |>.regionalFragmentEdges_eq_of_fragmentsOnFaceInRegion
        (regionalBoundaryGraphCutData_fragmentsOnFaceInRegion RS
          interface.localLayerRightPrefixRegion
          interface.nextLocalLayerPrefixCrossing)]
    rfl
  change min
      (interface.localLayerRightPrefixGraphCutData.regionalFragmentEdges
        index).card 5 = _
  rw [hfragmentEdges]
  rw [← interface.localLayerRightPrefixBoundaryFragmentEquiv_edges
    actualFragment]
  exact interface.localLayerRightPrefixBoundaryFragment_cap_eq_factorCaps
    (interface.localLayerRightPrefixBoundaryFragmentAt index)

end SourceConsecutiveSlabInterface

end AnnularEmbedding

end SourceTrail

end

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
