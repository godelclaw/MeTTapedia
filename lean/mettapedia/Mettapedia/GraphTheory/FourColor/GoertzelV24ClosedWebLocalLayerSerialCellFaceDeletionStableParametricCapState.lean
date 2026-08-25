import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePreRebaseState
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceExteriorLabelCapFactorUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationFaceInterfaceExteriorLabelCap

/-!
# A cap-parametric cumulative facial state

The published profile records face progress only up to five, but an internal
rolling state may need additional lookahead before a bounded interface
advance.  This file keeps that lookahead parameter explicit.  It extracts the
exact cumulative prefix code at an arbitrary cap and proves that adjoining one
literal Cell preserves exactness at the same cap.

The source's cap-seven state is one specialization.  The fixed forty-eight
dart Cell--rebase carrier also permits the conservative specialization at cap
fifty-three: every promoted dart is named by that carrier, so the generic
bounded-subtraction theorem can recover cap five without a boundary-locality
assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState

open GoertzelV24BoundedCarrierGraphFamilyCode
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAnnularEmbedding.ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebAtGoodWord.Instance.LocalLayerFormation
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePrefixState
open GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStablePreRebaseState
open GoertzelV24FaceOrbitIncidence
open GoertzelV24InterfaceExteriorLabelCapFactor
open GoertzelV24InterfaceExteriorLabelCapFactorUpdate
open GoertzelV24RotationFaceInterfaceExteriorLabelCap
open GoertzelV24RotationFaceRegionalDartGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance faceDeletionStableParametricCapEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- A fixed twenty-four-slot cumulative facial state with a caller-selected
exterior-component cap. -/
abbrev SourceLocalLayerSerialFaceDeletionStableParametricCapState
    (cap : Nat) :=
  BoundedInterfaceExteriorLabelCapFamilyCode 24 Unit cap

/-- Exact cap-parametric extraction on the rolling predecessor carrier. -/
noncomputable def sourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (cap : Nat) :
    SourceLocalLayerSerialFaceDeletionStableParametricCapState cap :=
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let dartAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  { vertexCount := ⟨carrier.card, Nat.lt_succ_of_le
      (sourceLocalLayerSerialFaceTransitionCarrierAt_card_le_twentyFour
        corridor hunique offset hcell)⟩
    code := fun _ => exactFaceInterfaceExteriorLabelCapCode web.annular.RS
      (sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset)
      dartAt cap }

@[simp]
theorem sourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt_vertexCount
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (cap : Nat) :
    (sourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt corridor
      hunique offset hcell cap).vertexCount.val =
        (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique offset
          ).card :=
  rfl

/-- Adjoin the literal Cell and its residual seam without changing the
selected exterior cap. -/
noncomputable def
    sourceLocalLayerSerialFaceDeletionStableParametricCapPreRebaseAt
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (cap : Nat) :
    SourceLocalLayerSerialFaceDeletionStableParametricCapState cap :=
  let prefixState :=
    sourceLocalLayerSerialFaceDeletionStableParametricCapPrefixAt corridor
      hunique offset hcell cap
  { vertexCount := prefixState.vertexCount
    code := fun _ =>
      addInterfaceAdjacencyAndPresence (prefixState.code ())
        (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset
          hcell)
        (fun slot => decide
          (web.annular.RS.edgeOf
              (((carrierCoordinate
                (sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
                  offset)).symm slot).1) ∈
            sourceLocalLayerCellRegionAt corridor hunique offset)) }

/-- The cap-parametric update is exactly the weighted pre-rebase regional
face code.  In particular this holds at the conservative cap fifty-three. -/
theorem
    sourceLocalLayerSerialFaceDeletionStableParametricCapPreRebaseAt_code_eq
    {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
    {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}
    {blockLength : Nat}
    (corridor : BoundaryCleanOrbitHexCorridor web.annular blockLength)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary web.annular.RS)
      (Finset.univ : Finset (OrbitFace web.annular.RS)))
    (offset : Fin (blockLength - 3))
    (hcell : (sourceLocalLayerCellRegionAt corridor hunique offset).card ≤ 6)
    (cap : Nat) :
    let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor
      hunique offset
    let dartAt := fun slot : Fin carrier.card =>
      ((carrierCoordinate carrier).symm slot).1
    (sourceLocalLayerSerialFaceDeletionStableParametricCapPreRebaseAt corridor
        hunique offset hcell cap).code () =
      exactFaceInterfaceExteriorLabelCapCode web.annular.RS
        (sourceLocalLayerSerialPreRebaseOutputRegionAt corridor hunique offset)
        dartAt cap := by
  dsimp only
  let carrier := sourceLocalLayerSerialFaceTransitionCarrierAt corridor hunique
    offset
  let dartAt := fun slot : Fin carrier.card =>
    ((carrierCoordinate carrier).symm slot).1
  let prefixRegion :=
    sourceLocalLayerSerialTerminalInputRegionAt corridor hunique offset
  let cellRegion := sourceLocalLayerCellRegionAt corridor hunique offset
  let prefixGraph := faceRegionalDartGraph web.annular.RS prefixRegion
  let localGraph := sourceLocalLayerSerialFaceLocalGraphAt corridor hunique
    offset
  have hupdate := addInterfaceAdjacencyAndPresence_exact_code_eq
    prefixGraph localGraph dartAt
    (sourceLocalLayerSerialFaceLocalGraph_support_subset_range corridor hunique
      offset)
    (fun dart => web.annular.RS.edgeOf dart ∈ prefixRegion)
    (fun dart => web.annular.RS.edgeOf dart ∈ cellRegion)
    Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
    web.annular.RS.edgeOf
    (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell)
    (sourceLocalLayerSerialFaceLocalAdjacency_exact corridor hunique offset
      hcell) cap
  change addInterfaceAdjacencyAndPresence
      (exactInterfaceExteriorLabelCapCode prefixGraph dartAt
        (fun dart => web.annular.RS.edgeOf dart ∈ prefixRegion)
        Prod.fst (faceInterfaceIncidenceVertex web.annular.RS dartAt)
        web.annular.RS.edgeOf cap)
      (sourceLocalLayerSerialFaceLocalAdjacencyAt corridor hunique offset hcell)
      (fun slot => decide
        (web.annular.RS.edgeOf (dartAt slot) ∈ cellRegion)) = _
  unfold exactFaceInterfaceExteriorLabelCapCode
  rw [sourceLocalLayerSerialPreRebaseFaceDartGraph_eq_three_factor corridor
    hunique offset, sup_assoc]
  rw [← sourceLocalLayerSerialTerminalInputRegionAt_union_cell corridor
    hunique offset]
  simpa only [prefixGraph, localGraph, prefixRegion, cellRegion,
    sourceLocalLayerSerialFaceLocalGraphAt, Finset.mem_union] using hupdate

/-- The conservative internal lookahead state used by the fixed 48-dart
rebase. -/
abbrev SourceLocalLayerSerialFaceDeletionStableWideCapState :=
  SourceLocalLayerSerialFaceDeletionStableParametricCapState 53

end

end GoertzelV24ClosedWebLocalLayerSerialCellFaceDeletionStableParametricCapState

end Mettapedia.GraphTheory.FourColor
